using Google.OrTools.Sat;

namespace SchedulePlanner.Core
{
    public interface IResultBuilder
    {
        ScheduleResult BuildResult(
            SchedulingContext context,
            ScheduleVariables variables,
            IReadOnlyList<RoomChangePenalty> penalties,
            SchedulerOptions config,
            CpSolver solver,
            CpSolverStatus status);
    }

    public sealed class ResultBuilder : IResultBuilder
    {
        public ScheduleResult BuildResult(
            SchedulingContext context,
            ScheduleVariables variables,
            IReadOnlyList<RoomChangePenalty> penalties,
            SchedulerOptions config,
            CpSolver solver,
            CpSolverStatus status)
        {
            var hasSolution = status is CpSolverStatus.Optimal or CpSolverStatus.Feasible;

            var teacherSchedules = new List<TeacherScheduleResult>();
            var classSummaries = new List<ClassScheduleSummary>();
            var roomChanges = new List<RoomChangeResult>();

            if (hasSolution)
            {
                foreach (var teacherEntry in context.TeacherGroups.Values)
                {
                    var days = new List<DayScheduleResult>();

                    for (var day = 0; day < context.NumDays; ++day)
                    {
                        var blocks = new List<BlockScheduleResult>();

                        for (var blockIndex = 0; blockIndex < context.BlocksPerDay; ++blockIndex)
                        {
                            if (teacherEntry.Classes.FirstOrDefault(entry =>
                                solver.BooleanValue(variables.Assignment[entry.Index, day, blockIndex])) is ClassAssignment assigned)
                            {
                                blocks.Add(new BlockScheduleResult(
                                    blockIndex,
                                    false,
                                    assigned.Config.Key,
                                    assigned.Config.Name,
                                    assigned.Room,
                                    assigned.Config.Department));
                            }
                            else if (config.PresetBlocks.FirstOrDefault(b => b.Index == blockIndex &&
                                b.Days.Contains(config.Days[day])) is PresetBlockConfig presetBlock)
                            {
                                blocks.Add(new BlockScheduleResult(
                                    blockIndex,
                                    false,
                                    presetBlock.Name,
                                    presetBlock.Name,
                                    null,
                                    "Preset"));
                            }
                            else
                            {
                                blocks.Add(new BlockScheduleResult(
                                    blockIndex,
                                    true,
                                    null,
                                    null,
                                    null,
                                    null));
                            }
                        }

                        days.Add(new DayScheduleResult(config.Days[day], blocks));
                    }

                    teacherSchedules.Add(new TeacherScheduleResult(
                        teacherEntry.Teacher.Id,
                        teacherEntry.Teacher.FullName,
                        days));
                }

                foreach (var entry in context.ClassAssignments)
                {
                    var scheduledBlocks = 0;

                    for (var day = 0; day < context.NumDays; ++day)
                    {
                        for (var block = 0; block < context.BlocksPerDay; ++block)
                        {
                            if (solver.BooleanValue(variables.Assignment[entry.Index, day, block]))
                            {
                                scheduledBlocks++;
                            }
                        }
                    }

                    classSummaries.Add(new ClassScheduleSummary(
                        entry.Config.Key,
                        entry.Config.Name,
                        entry.Config.Department,
                        entry.Teacher.Id,
                        entry.Teacher.FullName,
                        entry.Room,
                        scheduledBlocks,
                        entry.Config.WeeklyBlocks));
                }

                foreach (var penalty in penalties)
                {
                    if (!solver.BooleanValue(penalty.Var))
                    {
                        continue;
                    }

                    var teacherName = context.TeacherGroups.TryGetValue(penalty.TeacherId, out var teacherGroup)
                        ? teacherGroup.Teacher.FullName
                        : penalty.TeacherId;

                    roomChanges.Add(new RoomChangeResult(
                        penalty.TeacherId,
                        teacherName,
                        penalty.Day,
                        penalty.Block,
                        penalty.Block + 1,
                        penalty.FromClassKey,
                        penalty.FromRoom,
                        penalty.ToClassKey,
                        penalty.ToRoom));
                }
            }

            return new ScheduleResult(
                status.ToString(),
                hasSolution,
                hasSolution ? solver.ObjectiveValue : null,
                ParseSolverStatistics(hasSolution ? solver.ResponseStats() : string.Empty),
                teacherSchedules,
                classSummaries,
                roomChanges);
        }

        private static IReadOnlyList<SummaryItem> ParseSolverStatistics(string stats)
        {
            var lines = stats.Split('\n', StringSplitOptions.RemoveEmptyEntries);
            var statistics = new List<SummaryItem>();

            foreach (var line in lines)
            {
                var colonIndex = line.IndexOf(':');
                if (colonIndex > 0)
                {
                    var key = line[..colonIndex].Trim();
                    var value = line[(colonIndex + 1)..].Trim();
                    statistics.Add(new SummaryItem(key, value));
                }
                else if (!string.IsNullOrWhiteSpace(line))
                {
                    statistics.Add(new SummaryItem("Info", line.Trim()));
                }
            }

            return statistics;
        }
    }
}
