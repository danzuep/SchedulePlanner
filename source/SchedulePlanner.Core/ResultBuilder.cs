using Google.OrTools.Sat;
using System.Linq;

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
            CpSolverStatus status,
            TimeSpan runDuration);
    }

    public sealed class ResultBuilder : IResultBuilder
    {
        public ScheduleResult BuildResult(
            SchedulingContext context,
            ScheduleVariables variables,
            IReadOnlyList<RoomChangePenalty> penalties,
            SchedulerOptions config,
            CpSolver solver,
            CpSolverStatus status,
            TimeSpan runDuration)
        {
            var hasSolution = status is CpSolverStatus.Optimal or CpSolverStatus.Feasible;

            var teacherSchedules = new List<TeacherScheduleResult>();
            var classSummaries = new List<ClassScheduleSummary>();
            var roomChanges = new List<RoomChangeResult>();
            IReadOnlyList<RoomUtilization>? roomUtilizations = null;
            IReadOnlyList<StreamScheduleResult>? streamSchedules = null;

            if (hasSolution)
            {
                foreach (var teacherEntry in context.TeacherGroups.Values)
                {
                    var days = new List<DayScheduleResult>();

                    for (var day = 0; day < context.NumDays; ++day)
                    {
                        var blocks = new List<BlockScheduleResult>();

                        for (var blockIndex = 0; blockIndex < context.BlocksPerDayList[day]; ++blockIndex)
                        {
                            if (teacherEntry.Classes.FirstOrDefault(entry =>
                                solver.BooleanValue(variables.Assignment[entry.Index][day][blockIndex])) is ClassAssignment assigned)
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
                        for (var block = 0; block < context.BlocksPerDayList[day]; ++block)
                        {
                            if (solver.BooleanValue(variables.Assignment[entry.Index][day][block]))
                            {
                                scheduledBlocks++;
                            }
                        }
                    }

                    classSummaries.Add(new ClassScheduleSummary(
                        entry.Config.Key,
                        entry.Config.Name,
                        entry.Config.Department,
                        entry.Teachers.First().Id,
                        entry.Teachers.First().FullName,
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

                roomUtilizations = CalculateRoomUtilizations(context, variables, config, solver);
                streamSchedules = BuildStreamSchedules(context, variables, config, solver);
            }

            return new ScheduleResult(
                hasSolution ? "Optimal" : "Infeasible",
                hasSolution,
                hasSolution ? solver.ObjectiveValue : null,
                new[] { new SummaryItem("SolverStatus", status.ToString()) },
                teacherSchedules,
                classSummaries,
                roomChanges,
                roomUtilizations,
                streamSchedules,
                runDuration);
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

        private static IReadOnlyList<RoomUtilization> CalculateRoomUtilizations(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            CpSolver solver)
        {
            var utilizations = new List<RoomUtilization>();
            var totalSlots = context.BlocksPerDayList.Sum();

            foreach (var roomGroup in context.RoomGroups)
            {
                var roomId = roomGroup.Key;
                var assignedSlots = 0;

                foreach (var assignment in roomGroup.Value)
                {
                    for (var day = 0; day < context.NumDays; ++day)
                    {
                        for (var block = 0; block < context.BlocksPerDayList[day]; ++block)
                        {
                            if (solver.BooleanValue(variables.Assignment[assignment.Index][day][block]))
                            {
                                assignedSlots++;
                            }
                        }
                    }
                }

                var utilization = totalSlots > 0 ? (double)assignedSlots / totalSlots * 100 : 0;
                utilizations.Add(new RoomUtilization(roomId, utilization));
            }

            return utilizations;
        }

        private static IReadOnlyList<StreamScheduleResult> BuildStreamSchedules(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            CpSolver solver)
        {
            var streamSchedules = new List<StreamScheduleResult>();

            foreach (var assignment in context.ClassAssignments.Where(a => a.ClassStream != null))
            {
                var stream = assignment.ClassStream!;
                var days = new List<DayScheduleResult>();

                for (var day = 0; day < context.NumDays; ++day)
                {
                    var blocks = new List<BlockScheduleResult>();

                    for (var blockIndex = 0; blockIndex < context.BlocksPerDayList[day]; ++blockIndex)
                    {
                        if (solver.BooleanValue(variables.Assignment[assignment.Index][day][blockIndex]))
                        {
                            blocks.Add(new BlockScheduleResult(
                                blockIndex,
                                false,
                                assignment.Config.Key,
                                assignment.Config.Name,
                                assignment.Room,
                                assignment.Config.Department));
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

                streamSchedules.Add(new StreamScheduleResult(
                    stream.Id,
                    assignment.Config.Key,
                    assignment.Teachers.First().Id,
                    assignment.Room,
                    days));
            }

            return streamSchedules;
        }
    }
}
