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
    }

    public sealed record SchedulingContext(
        CpModel Model,
        IReadOnlyList<ClassAssignment> ClassAssignments,
        IReadOnlyDictionary<string, TeacherGroup> TeacherGroups,
        IReadOnlyDictionary<string, IReadOnlyList<ClassAssignment>> RoomGroups,
        int NumDays,
        int BlocksPerDay);

    public sealed record ScheduleVariables(BoolVar[,,] Assignment);
}
