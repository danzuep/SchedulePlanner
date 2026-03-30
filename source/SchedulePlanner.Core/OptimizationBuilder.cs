using Google.OrTools.Sat;

namespace SchedulePlanner.Core
{
    public interface IOptimizationBuilder
    {
        IReadOnlyList<RoomChangePenalty> AddRoomChangeOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int roomChangePenaltyWeight,
            CancellationToken cancellationToken);

        IReadOnlyList<ScheduleSpreadPenalty> AddScheduleSpreadOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int scheduleSpreadPenaltyWeight,
            CancellationToken cancellationToken);
    }

    public sealed class OptimizationBuilder : IOptimizationBuilder
    {
        public IReadOnlyList<RoomChangePenalty> AddRoomChangeOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int roomChangePenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<RoomChangePenalty>();

            for (var day = 0; day < context.NumDays; ++day)
            {
                cancellationToken.ThrowIfCancellationRequested();

                for (var block = 0; block < context.BlocksPerDay - 1; ++block)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    foreach (var teacherEntry in context.TeacherGroups)
                    {
                        cancellationToken.ThrowIfCancellationRequested();

                        var teacherId = teacherEntry.Key;
                        var classes = teacherEntry.Value.Classes;

                        foreach (var current in classes)
                        {
                            cancellationToken.ThrowIfCancellationRequested();

                            foreach (var next in classes)
                            {
                                cancellationToken.ThrowIfCancellationRequested();

                                if (current.Room == next.Room)
                                {
                                    continue;
                                }

                                var penaltyVar = context.Model.NewBoolVar(
                                    $"room_change_{teacherId}_day{day}_block{block}_{current.Config.Key}_{next.Config.Key}");

                                context.Model.Add(penaltyVar <= variables.Assignment[current.Index, day, block]);
                                context.Model.Add(penaltyVar <= variables.Assignment[next.Index, day, block + 1]);
                                context.Model.Add(
                                    penaltyVar >= variables.Assignment[current.Index, day, block]
                                                + variables.Assignment[next.Index, day, block + 1]
                                                - 1);

                                penalties.Add(new RoomChangePenalty(
                                    penaltyVar,
                                    teacherId,
                                    config.Days[day],
                                    block,
                                    current.Config.Key,
                                    current.Room,
                                    next.Config.Key,
                                    next.Room));
                            }
                        }
                    }
                }
            }

            return penalties;
        }

        public IReadOnlyList<ScheduleSpreadPenalty> AddScheduleSpreadOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int scheduleSpreadPenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<ScheduleSpreadPenalty>();

            for (var day = 0; day < context.NumDays; ++day)
            {
                cancellationToken.ThrowIfCancellationRequested();

                for (var block = 0; block < context.BlocksPerDay - 2; ++block)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    foreach (var teacherEntry in context.TeacherGroups)
                    {
                        cancellationToken.ThrowIfCancellationRequested();

                        var teacherId = teacherEntry.Key;
                        var classes = teacherEntry.Value.Classes;

                        foreach (var current in classes)
                        {
                            cancellationToken.ThrowIfCancellationRequested();

                            foreach (var next in classes)
                            {
                                cancellationToken.ThrowIfCancellationRequested();

                                if (current == next)
                                {
                                    continue;
                                }

                                var penaltyVar = context.Model.NewBoolVar(
                                    $"schedule_spread_{teacherId}_day{day}_block{block}_{current.Config.Key}_{next.Config.Key}");

                                context.Model.Add(penaltyVar <= variables.Assignment[current.Index, day, block]);
                                context.Model.Add(penaltyVar <= variables.Assignment[next.Index, day, block + 2]);
                                context.Model.Add(
                                    penaltyVar >= variables.Assignment[current.Index, day, block]
                                                + variables.Assignment[next.Index, day, block + 2]
                                                - 1);

                                penalties.Add(new ScheduleSpreadPenalty(
                                    penaltyVar,
                                    teacherId,
                                    config.Days[day],
                                    block,
                                    current.Config.Key,
                                    next.Config.Key));
                            }
                        }
                    }
                }
            }

            return penalties;
        }
    }

    public sealed record RoomChangePenalty(
        BoolVar Var,
        string TeacherId,
        DayOfWeek Day,
        int Block,
        string FromClassKey,
        string FromRoom,
        string ToClassKey,
        string ToRoom);

    public sealed record ScheduleSpreadPenalty(
        BoolVar Var,
        string TeacherId,
        DayOfWeek Day,
        int Block,
        string FromClassKey,
        string ToClassKey);
}
