using Google.OrTools.Sat;

namespace SchedulePlanner.Core
{
    public interface IConstraintBuilder
    {
        void AddSchedulingRules(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            CancellationToken cancellationToken);
    }

    public sealed class ConstraintBuilder : IConstraintBuilder
    {
        public void AddSchedulingRules(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            CancellationToken cancellationToken)
        {
            RequireEachClassToBeScheduledForItsWeeklyBlocks(context, variables, cancellationToken);
            PreventTeachersFromBeingDoubleBooked(context, variables, cancellationToken);
            PreventRoomsFromBeingDoubleBooked(context, variables, cancellationToken);
            PreventSchedulingInDefaultBlocks(context, variables, config, cancellationToken);
            PreventStreamConflicts(context, variables, cancellationToken);
            PreventRoomBufferConflicts(context, variables, config, cancellationToken);
            PreventUnavailableScheduling(context, variables, config, cancellationToken);
        }

        private void PreventSchedulingInDefaultBlocks(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            CancellationToken cancellationToken)
        {
            if (config.PresetBlocks == null || !config.PresetBlocks.Any())
            {
                return;
            }

            foreach (var defaultBlock in config.PresetBlocks)
            {
                cancellationToken.ThrowIfCancellationRequested();

                if (defaultBlock.Index < 0 || defaultBlock.Index >= context.BlocksPerDay)
                {
                    continue;
                }

                foreach (var day in defaultBlock.Days)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    var dayIndex = -1;
                    for (var i = 0; i < config.Days.Count; i++)
                    {
                        if (config.Days[i] == day)
                        {
                            dayIndex = i;
                            break;
                        }
                    }

                    if (dayIndex < 0)
                    {
                        continue;
                    }

                    foreach (var entry in context.ClassAssignments)
                    {
                        cancellationToken.ThrowIfCancellationRequested();
                        context.Model.Add(variables.Assignment[entry.Index, dayIndex, defaultBlock.Index] == 0);
                    }
                }
            }
        }

        private void RequireEachClassToBeScheduledForItsWeeklyBlocks(
            SchedulingContext context,
            ScheduleVariables variables,
            CancellationToken cancellationToken)
        {
            foreach (var entry in context.ClassAssignments)
            {
                cancellationToken.ThrowIfCancellationRequested();

                var allSlots = new List<BoolVar>();

                for (var day = 0; day < context.NumDays; ++day)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    for (var block = 0; block < context.BlocksPerDay; ++block)
                    {
                        cancellationToken.ThrowIfCancellationRequested();
                        allSlots.Add(variables.Assignment[entry.Index, day, block]);
                    }
                }

                if (entry.Config.WeeklyBlocks > context.NumDays * context.BlocksPerDay)
                {
                    throw new InvalidOperationException(
                        $"Class {entry.Config.Key} demands more blocks than available.");
                }

                context.Model.Add(LinearExpr.Sum(allSlots) == entry.Config.WeeklyBlocks);
            }
        }

        private void PreventTeachersFromBeingDoubleBooked(
            SchedulingContext context,
            ScheduleVariables variables,
            CancellationToken cancellationToken)
        {
            foreach (var teacherGroup in context.TeacherGroups.Values)
            {
                cancellationToken.ThrowIfCancellationRequested();

                for (var day = 0; day < context.NumDays; ++day)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    for (var block = 0; block < context.BlocksPerDay; ++block)
                    {
                        cancellationToken.ThrowIfCancellationRequested();

                        var slots = teacherGroup.Classes
                            .Select(entry => variables.Assignment[entry.Index, day, block])
                            .ToList();

                        if (slots.Count > 1)
                        {
                            context.Model.AddAtMostOne(slots);
                        }
                    }
                }
            }
        }

        private void PreventRoomsFromBeingDoubleBooked(
            SchedulingContext context,
            ScheduleVariables variables,
            CancellationToken cancellationToken)
        {
            foreach (var roomClasses in context.RoomGroups.Values)
            {
                cancellationToken.ThrowIfCancellationRequested();

                for (var day = 0; day < context.NumDays; ++day)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    for (var block = 0; block < context.BlocksPerDay; ++block)
                    {
                        cancellationToken.ThrowIfCancellationRequested();

                        var slots = roomClasses
                            .Select(entry => variables.Assignment[entry.Index, day, block])
                            .ToList();

                        if (slots.Count > 1)
                        {
                            context.Model.AddAtMostOne(slots);
                        }
                    }
                }
            }
        }

        private void PreventStreamConflicts(
            SchedulingContext context,
            ScheduleVariables variables,
            CancellationToken cancellationToken)
        {
            var streamedAssignments = context.ClassAssignments
                .Where(a => a.Stream != null)
                .ToList();

            for (var i = 0; i < streamedAssignments.Count; ++i)
            {
                for (var j = i + 1; j < streamedAssignments.Count; ++j)
                {
                    var stream1 = streamedAssignments[i].Stream!;
                    var stream2 = streamedAssignments[j].Stream!;

                    // Check if streams have intersecting linked subjects
                    var intersect = stream1.LinkedSubjects.Intersect(stream2.LinkedSubjects, StringComparer.OrdinalIgnoreCase);
                    if (intersect.Any())
                    {
                        // Prevent overlap
                        for (var day = 0; day < context.NumDays; ++day)
                        {
                            for (var block = 0; block < context.BlocksPerDay; ++block)
                            {
                                context.Model.Add(
                                    variables.Assignment[streamedAssignments[i].Index, day, block] +
                                    variables.Assignment[streamedAssignments[j].Index, day, block] <= 1);
                            }
                        }
                    }
                }
            }
        }

        private void PreventRoomBufferConflicts(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            CancellationToken cancellationToken)
        {
            foreach (var roomGroup in context.RoomGroups)
            {
                cancellationToken.ThrowIfCancellationRequested();

                var roomId = roomGroup.Key;
                var buffer = GetRoomBuffer(config, roomId);
                if (buffer <= 0) continue;

                var roomClasses = roomGroup.Value;

                for (var day = 0; day < context.NumDays; ++day)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    for (var b = 0; b < context.BlocksPerDay - buffer; ++b)
                    {
                        cancellationToken.ThrowIfCancellationRequested();

                        var assignedAtB = roomClasses
                            .Select(entry => variables.Assignment[entry.Index, day, b])
                            .ToList();

                        var assignedAtBPlus = roomClasses
                            .Select(entry => variables.Assignment[entry.Index, day, b + buffer])
                            .ToList();

                        context.Model.Add(LinearExpr.Sum(assignedAtB) + LinearExpr.Sum(assignedAtBPlus) <= 1);
                    }
                }
            }
        }

        private static int GetRoomBuffer(SchedulerOptions config, string roomId)
        {
            return config.Rooms.FirstOrDefault(r => r.Id == roomId)?.SetupTimeBuffer ?? 0;
        }

        private void PreventUnavailableScheduling(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            CancellationToken cancellationToken)
        {
            foreach (var teacherEntry in context.TeacherGroups.Values)
            {
                cancellationToken.ThrowIfCancellationRequested();

                var teacher = teacherEntry.Teacher;
                if (teacher.AvailabilityPatterns.Count == 0) continue;

                var availableDays = new HashSet<DayOfWeek>(teacher.AvailabilityPatterns);

                for (var dayIndex = 0; dayIndex < context.NumDays; ++dayIndex)
                {
                    var day = config.Days[dayIndex];
                    if (!availableDays.Contains(day))
                    {
                        foreach (var cls in teacherEntry.Classes)
                        {
                            for (var block = 0; block < context.BlocksPerDay; ++block)
                            {
                                context.Model.Add(variables.Assignment[cls.Index, dayIndex, block] == 0);
                            }
                        }
        }
    }
            }
        }
    }

    public sealed record SchedulingContext(
        CpModel Model,
        IReadOnlyList<ClassAssignment> ClassAssignments,
        IReadOnlyDictionary<string, TeacherGroup> TeacherGroups,
        IReadOnlyDictionary<string, IReadOnlyList<ClassAssignment>> RoomGroups,
        int NumDays,
        IReadOnlyList<int> BlocksPerDayList);

    public sealed record ScheduleVariables(BoolVar[][][] Assignment);
}
