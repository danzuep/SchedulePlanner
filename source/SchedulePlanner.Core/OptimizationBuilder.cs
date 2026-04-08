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

        IReadOnlyList<WeekDistributionPenalty> AddWeekDistributionOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int weekDistributionPenaltyWeight,
            CancellationToken cancellationToken);

        IReadOnlyList<ClassDayClusteringPenalty> AddClassDayClusteringOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int classDayClusteringPenaltyWeight,
            CancellationToken cancellationToken);

        IReadOnlyList<ClassBlockConsistencyPenalty> AddClassBlockConsistencyOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int classBlockConsistencyPenaltyWeight,
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

                                if (current == next)
                                {
                                    continue;
                                }

                                var penaltyVar = context.Model.NewBoolVar(
                                    $"schedule_spread_{teacherId}_day{day}_block{block}_{current.Config.Key}_{next.Config.Key}");

                                context.Model.Add(penaltyVar <= variables.Assignment[current.Index, day, block]);
                                context.Model.Add(penaltyVar <= variables.Assignment[next.Index, day, block + 1]);
                                context.Model.Add(
                                    penaltyVar >= variables.Assignment[current.Index, day, block]
                                                + variables.Assignment[next.Index, day, block + 1]
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

        public IReadOnlyList<WeekDistributionPenalty> AddWeekDistributionOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int weekDistributionPenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<WeekDistributionPenalty>();

            foreach (var teacherEntry in context.TeacherGroups)
            {
                cancellationToken.ThrowIfCancellationRequested();

                var teacherId = teacherEntry.Key;
                var classes = teacherEntry.Value.Classes;

                for (var d = 0; d < context.NumDays - 1; ++d)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    var sumDayD = new List<LinearExpr>();
                    var sumDayD1 = new List<LinearExpr>();

                    foreach (var cls in classes)
                    {
                        for (var block = 0; block < context.BlocksPerDay; ++block)
                        {
                            sumDayD.Add(variables.Assignment[cls.Index, d, block]);
                            sumDayD1.Add(variables.Assignment[cls.Index, d + 1, block]);
                        }
                    }

                    var penaltyVar = context.Model.NewBoolVar(
                        $"week_distribution_{teacherId}_day{d}_to_day{d + 1}");

                    context.Model.Add(LinearExpr.Sum(sumDayD1) >= LinearExpr.Sum(sumDayD) + 1).OnlyEnforceIf(penaltyVar);
                    context.Model.Add(LinearExpr.Sum(sumDayD1) < LinearExpr.Sum(sumDayD) + 1).OnlyEnforceIf(penaltyVar.Not());

                    penalties.Add(new WeekDistributionPenalty(
                        penaltyVar,
                        teacherId,
                        config.Days[d],
                        config.Days[d + 1]));
                }
            }

            return penalties;
        }

        public IReadOnlyList<ClassDayClusteringPenalty> AddClassDayClusteringOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int classDayClusteringPenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<ClassDayClusteringPenalty>();

            foreach (var classAssignment in context.ClassAssignments)
            {
                cancellationToken.ThrowIfCancellationRequested();

                for (var day = 0; day < context.NumDays; ++day)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    var daySlots = new List<LinearExpr>();
                    for (var block = 0; block < context.BlocksPerDay; ++block)
                    {
                        daySlots.Add(variables.Assignment[classAssignment.Index, day, block]);
                    }

                    var penaltyVar = context.Model.NewBoolVar(
                        $"class_day_clustering_{classAssignment.Config.Key}_day{day}");

                    context.Model.Add(LinearExpr.Sum(daySlots) >= 2).OnlyEnforceIf(penaltyVar);
                    context.Model.Add(LinearExpr.Sum(daySlots) < 2).OnlyEnforceIf(penaltyVar.Not());

                    penalties.Add(new ClassDayClusteringPenalty(
                        penaltyVar,
                        classAssignment.Config.Key,
                        config.Days[day]));
                }
            }

            return penalties;
        }

        public IReadOnlyList<ClassBlockConsistencyPenalty> AddClassBlockConsistencyOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int classBlockConsistencyPenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<ClassBlockConsistencyPenalty>();

            foreach (var classAssignment in context.ClassAssignments)
            {
                cancellationToken.ThrowIfCancellationRequested();

                for (var block = 0; block < context.BlocksPerDay; ++block)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    var blockAssignments = new List<LinearExpr>();
                    for (var day = 0; day < context.NumDays; ++day)
                    {
                        blockAssignments.Add(variables.Assignment[classAssignment.Index, day, block]);
                    }

                    var penaltyVar = context.Model.NewBoolVar(
                        $"class_block_consistency_{classAssignment.Config.Key}_block{block}");

                    context.Model.Add(LinearExpr.Sum(blockAssignments) >= 1).OnlyEnforceIf(penaltyVar);
                    context.Model.Add(LinearExpr.Sum(blockAssignments) < 1).OnlyEnforceIf(penaltyVar.Not());

                    penalties.Add(new ClassBlockConsistencyPenalty(
                        penaltyVar,
                        classAssignment.Config.Key,
                        block));
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

    public sealed record WeekDistributionPenalty(
        BoolVar Var,
        string TeacherId,
        DayOfWeek FromDay,
        DayOfWeek ToDay);

    public sealed record ClassDayClusteringPenalty(
        BoolVar Var,
        string ClassKey,
        DayOfWeek Day);

    public sealed record ClassBlockConsistencyPenalty(
        BoolVar Var,
        string ClassKey,
        int Block);
}
