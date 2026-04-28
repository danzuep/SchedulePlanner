using Google.OrTools.Sat;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using Microsoft.Extensions.Options;

namespace SchedulePlanner.Core
{
    public interface IService
    {
        Task RunAsync(CancellationToken cancellationToken = default);
    }

    public interface IService<T>
    {
        Task<T> RunAsync(CancellationToken cancellationToken = default);
    }

    public sealed class SchedulingService : IService<ScheduleResult>
    {
        public SchedulerOptions Config => _config;

        private readonly SchedulerOptions _config;
        private readonly ILogger<SchedulingService> _logger;
        private readonly IConfigValidator _configValidator;
        private readonly IClassAssignmentBuilder _classAssignmentBuilder;
        private readonly IConstraintBuilder _constraintBuilder;
        private readonly IOptimizationBuilder _optimizationBuilder;
        private readonly IResultBuilder _resultBuilder;
        private readonly IScheduleLogger _scheduleLogger;

        public SchedulingService(
            IOptions<SchedulerOptions> config,
            ILogger<SchedulingService>? logger = null,
            IConfigValidator? configValidator = null,
            IClassAssignmentBuilder? classAssignmentBuilder = null,
            IConstraintBuilder? constraintBuilder = null,
            IOptimizationBuilder? optimizationBuilder = null,
            IResultBuilder? resultBuilder = null,
            IScheduleLogger? scheduleLogger = null)
        {
            _config = config.Value;
            _logger = logger ?? NullLogger<SchedulingService>.Instance;
            _configValidator = configValidator ?? new ConfigValidator();
            _classAssignmentBuilder = classAssignmentBuilder ?? new ClassAssignmentBuilder();
            _constraintBuilder = constraintBuilder ?? new ConstraintBuilder();
            _optimizationBuilder = optimizationBuilder ?? new OptimizationBuilder();
            _resultBuilder = resultBuilder ?? new ResultBuilder();
            _scheduleLogger = scheduleLogger ?? new ScheduleLogger();
        }

        public Task<ScheduleResult> RunAsync(CancellationToken cancellationToken = default)
        {
            var normalized = _configValidator.ValidateAndNormalizeConfig(_config);

            _logger.LogInformation(
                "Building timetable for {Days} days with {Blocks} blocks per day.",
                _config.Days.Count,
                _config.BlocksPerDay);

            var context = BuildSchedulingContext(cancellationToken);
            var variables = CreateDecisionVariables(context, cancellationToken);

            // Fix pre-assigned slots
            foreach (var slot in _config.PreAssignedSlots)
            {
                if (slot.AssignmentIndex >= 0 && slot.AssignmentIndex < context.ClassAssignments.Count &&
                    slot.Day >= 0 && slot.Day < context.NumDays &&
                    slot.Block >= 0 && slot.Block < context.BlocksPerDay)
                {
                    context.Model.Add(variables.Assignment[slot.AssignmentIndex, slot.Day, slot.Block] == 1);
                }
                else
                {
                    throw new InvalidOperationException($"Invalid pre-assigned slot: Assignment {slot.AssignmentIndex}, Day {slot.Day}, Block {slot.Block}");
                }
            }

            // Set hints from previous solution for incremental solving
            if (_config.PreviousScheduleResult != null)
            {
                SetHintsFromPreviousSolution(context, variables, _config.PreviousScheduleResult);
            }

            _constraintBuilder.AddSchedulingRules(context, variables, _config, cancellationToken);
            var penalties = _optimizationBuilder.AddRoomChangeOptimization(context, variables, _config, normalized.RoomChangePenalty, cancellationToken);
            var spreadPenalties = _optimizationBuilder.AddScheduleSpreadOptimization(context, variables, _config, normalized.ScheduleSpreadPenalty, cancellationToken);
            var weekDistPenalties = _optimizationBuilder.AddWeekDistributionOptimization(context, variables, _config, normalized.WeekDistributionPenalty, cancellationToken);
            var classDayClusteringPenalties = _optimizationBuilder.AddClassDayClusteringOptimization(context, variables, _config, normalized.ClassDayClusteringPenalty, cancellationToken);
            var classBlockConsistencyPenalties = _optimizationBuilder.AddClassBlockConsistencyOptimization(context, variables, _config, normalized.ClassBlockConsistencyPenalty, cancellationToken);
            var streamFragmentationPenalties = _optimizationBuilder.AddStreamFragmentationOptimization(context, variables, _config, normalized.StreamFragmentationPenalty, cancellationToken);
            var sharedRoomChangePenalties = _optimizationBuilder.AddSharedRoomChangeOptimization(context, variables, _config, normalized.SharedRoomChangePenalty, cancellationToken);
            var targetLoadAdherencePenalties = _optimizationBuilder.AddTargetLoadAdherenceOptimization(context, variables, _config, normalized.TargetLoadAdherencePenalty, cancellationToken);
            var studentRoomTransitionPenalties = _optimizationBuilder.AddStudentRoomTransitionOptimization(context, variables, _config, normalized.StudentRoomTransitionPenalty, cancellationToken);
            var mergedBlockConsistencyPenalties = _optimizationBuilder.AddMergedBlockConsistencyOptimization(context, variables, _config, normalized.MergedBlockConsistencyPenalty, cancellationToken);
            var freeTimePenalties = _optimizationBuilder.AddFreeTimeOptimization(context, variables, _config, normalized.FreeTimePenalty, cancellationToken);

            // Combine all penalties for minimization
            var allPenaltyVars = penalties.Select(x => x.Var)
                .Concat(spreadPenalties.Select(x => x.Var))
                .Concat(weekDistPenalties.Select(x => x.Var))
                .Concat(classDayClusteringPenalties.Select(x => x.Var))
                .Concat(classBlockConsistencyPenalties.Select(x => x.Var))
                .Concat(streamFragmentationPenalties.Select(x => x.Var))
                .Concat(sharedRoomChangePenalties.Select(x => x.Var))
                .Concat(targetLoadAdherencePenalties.Select(x => x.Var))
                .Concat(studentRoomTransitionPenalties.Select(x => x.Var))
                .Concat(mergedBlockConsistencyPenalties.Select(x => x.Var))
                .Concat(freeTimePenalties.Select(x => x.Var))
                .ToArray();
            var allPenaltyWeights = Enumerable.Repeat(normalized.RoomChangePenalty, penalties.Count)
                .Concat(Enumerable.Repeat(normalized.ScheduleSpreadPenalty, spreadPenalties.Count))
                .Concat(Enumerable.Repeat(normalized.WeekDistributionPenalty, weekDistPenalties.Count))
                .Concat(Enumerable.Repeat(normalized.ClassDayClusteringPenalty, classDayClusteringPenalties.Count))
                .Concat(Enumerable.Repeat(normalized.ClassBlockConsistencyPenalty, classBlockConsistencyPenalties.Count))
                .Concat(Enumerable.Repeat(normalized.StreamFragmentationPenalty, streamFragmentationPenalties.Count))
                .Concat(Enumerable.Repeat(normalized.SharedRoomChangePenalty, sharedRoomChangePenalties.Count))
                .Concat(Enumerable.Repeat(normalized.TargetLoadAdherencePenalty, targetLoadAdherencePenalties.Count))
                .Concat(Enumerable.Repeat(normalized.StudentRoomTransitionPenalty, studentRoomTransitionPenalties.Count))
                .Concat(Enumerable.Repeat(normalized.MergedBlockConsistencyPenalty, mergedBlockConsistencyPenalties.Count))
                .Concat(Enumerable.Repeat(normalized.FreeTimePenalty, freeTimePenalties.Count))
                .ToArray();

            context.Model.Minimize(
                LinearExpr.WeightedSum(allPenaltyVars.Cast<LinearExpr>(), allPenaltyWeights));

            var solver = CreateSolver(normalized.SolverTimeLimitSeconds);
            var status = solver.Solve(context.Model);

            var result = _resultBuilder.BuildResult(context, variables, penalties, _config, solver, status);

            _scheduleLogger.LogResult(result);

            return Task.FromResult(result);
        }

        private SchedulingContext BuildSchedulingContext(CancellationToken cancellationToken)
        {
            var classAssignments = _classAssignmentBuilder.BuildClassAssignments(_config);
            var teacherGroups = _classAssignmentBuilder.BuildTeacherGroups(classAssignments);
            var roomGroups = _classAssignmentBuilder.BuildRoomGroups(classAssignments);

            var blocksPerDayList = _config.DayConfigs.Any()
                ? _config.DayConfigs.OrderBy(dc => dc.Day).Select(dc => dc.BlocksPerDay).ToList()
                : Enumerable.Repeat(_config.BlocksPerDay, _config.Days.Count).ToList();

            return new SchedulingContext(
                new CpModel(),
                classAssignments,
                teacherGroups,
                roomGroups,
                _config.Days.Count,
                blocksPerDayList);
        }

        private ScheduleVariables CreateDecisionVariables(SchedulingContext context, CancellationToken cancellationToken)
        {
            var assignment = new BoolVar[context.ClassAssignments.Count][][];

            for (var cls = 0; cls < context.ClassAssignments.Count; ++cls)
            {
                cancellationToken.ThrowIfCancellationRequested();

                assignment[cls] = new BoolVar[context.NumDays][];
                for (var day = 0; day < context.NumDays; ++day)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    assignment[cls][day] = new BoolVar[context.BlocksPerDayList[day]];
                    for (var block = 0; block < context.BlocksPerDayList[day]; ++block)
                    {
                        cancellationToken.ThrowIfCancellationRequested();

                        assignment[cls][day][block] = context.Model.NewBoolVar(
                            $"assign_{context.ClassAssignments[cls].Config.Key}_day{day}_block{block}");
                    }
                }
            }

            return new ScheduleVariables(assignment);
        }

        private static void SetHintsFromPreviousSolution(SchedulingContext context, ScheduleVariables variables, ScheduleResult previous)
        {
            // Set hints based on previous solution to aid incremental solving
            // Assume same assignment structure
            for (int assignmentIndex = 0; assignmentIndex < context.ClassAssignments.Count; assignmentIndex++)
            {
                var assignment = context.ClassAssignments[assignmentIndex];
                var teacherId = assignment.Teachers.First().Id;

                var prevTeacher = previous.TeacherSchedules.FirstOrDefault(t => t.TeacherId == teacherId);
                if (prevTeacher == null) continue;

                for (int day = 0; day < context.NumDays && day < prevTeacher.Days.Count; day++)
                {
                    var prevDay = prevTeacher.Days[day];
                    for (int block = 0; block < context.BlocksPerDay && block < prevDay.Blocks.Count; block++)
                    {
                        var prevBlock = prevDay.Blocks[block];
                        // Find if this assignment was scheduled in previous
                        if (!prevBlock.IsFree && prevBlock.ClassKey == assignment.Config.Key)
                        {
                            context.Model.AddHint(variables.Assignment[assignmentIndex, day, block], 1);
                        }
                    }
                }
            }
        }

        private static CpSolver CreateSolver(double solverTimeLimitSeconds)
        {
            return new CpSolver
            {
                StringParameters = $"max_time_in_seconds:{solverTimeLimitSeconds}"
            };
        }
    }

    public sealed record SummaryItem(string Key, string Value);

    public static class ScheduleResultExtensions
    {
        public static WhatIfComparison CompareWith(this ScheduleResult baseline, ScheduleResult whatIf)
        {
            var differences = new List<string>();

            // Compare objective
            if (baseline.ObjectiveValue != whatIf.ObjectiveValue)
            {
                differences.Add($"Objective changed: {baseline.ObjectiveValue} -> {whatIf.ObjectiveValue}");
            }

            // Compare teacher schedules
            var baselineTeachers = baseline.TeacherSchedules.ToDictionary(t => t.TeacherId);
            var whatIfTeachers = whatIf.TeacherSchedules.ToDictionary(t => t.TeacherId);

            foreach (var teacher in baselineTeachers.Keys.Union(whatIfTeachers.Keys))
            {
                if (!baselineTeachers.TryGetValue(teacher, out var baseTeacher))
                {
                    differences.Add($"New teacher: {teacher}");
                    continue;
                }
                if (!whatIfTeachers.TryGetValue(teacher, out var whatTeacher))
                {
                    differences.Add($"Removed teacher: {teacher}");
                    continue;
                }

                // Compare schedules (simplified)
                var baseBlocks = baseTeacher.Days.SelectMany(d => d.Blocks).Count(b => !b.IsFree);
                var whatBlocks = whatTeacher.Days.SelectMany(d => d.Blocks).Count(b => !b.IsFree);
                if (baseBlocks != whatBlocks)
                {
                    differences.Add($"Teacher {teacher} blocks: {baseBlocks} -> {whatBlocks}");
                }
            }

            // Similar for classes, rooms, etc.

            return new WhatIfComparison(differences);
        }
    }

    public sealed record WhatIfComparison(IReadOnlyList<string> Differences);

    public sealed record ScheduleResult(
        string Status,
        bool HasSolution,
        double? ObjectiveValue,
        IReadOnlyList<SummaryItem> SolverStatistics,
        IReadOnlyList<TeacherScheduleResult> TeacherSchedules,
        IReadOnlyList<ClassScheduleSummary> Classes,
        IReadOnlyList<RoomChangeResult> RoomChanges,
        IReadOnlyList<RoomUtilization> RoomUtilizations,
        IReadOnlyList<StreamScheduleResult> StreamSchedules);

    public sealed record TeacherScheduleResult(
        string TeacherId,
        string TeacherName,
        IReadOnlyList<DayScheduleResult> Days);

    public sealed record DayScheduleResult(
        DayOfWeek Day,
        IReadOnlyList<BlockScheduleResult> Blocks);

    public sealed record BlockScheduleResult(
        int Block,
        bool IsFree,
        string? ClassKey,
        string? ClassName,
        string? Room,
        string? Department);

    public sealed record ClassScheduleSummary(
        string ClassKey,
        string ClassName,
        string Department,
        string TeacherId,
        string TeacherName,
        string Room,
        int ScheduledBlocks,
        int RequiredBlocks);

    public sealed record RoomUtilization(
        string RoomId,
        double UtilizationPercent);

    public sealed record StreamScheduleResult(
        string StreamId,
        string ClassKey,
        string TeacherId,
        string Room,
        IReadOnlyList<DayScheduleResult> Days);

    public sealed record RoomChangeResult(
        string TeacherId,
        string TeacherName,
        DayOfWeek Day,
        int FromBlock,
        int ToBlock,
        string FromClassKey,
        string FromRoom,
        string ToClassKey,
        string ToRoom);

    public sealed record WeekScheduleResult(
        Teacher Teacher,
        IReadOnlyList<ScheduleBlockResult> Blocks);

    public sealed record ScheduleBlockResult(
        BlockMetadata Block,
        ClassMetadata? Monday,
        ClassMetadata? Tuesday,
        ClassMetadata? Wednesday,
        ClassMetadata? Thursday,
        ClassMetadata? Friday);

    public sealed record BlockMetadata(
        int Block,
        string BlockName,
        string? BlockTimeRange,
        string? Room)
    {
        public override string ToString() => BlockName;
    }

    public sealed record ClassMetadata(
        string ClassKey,
        string ClassName,
        string Department,
        string? Room)
    {
        public override string ToString() => ClassKey;
    }

    public static class TeacherScheduleResultExtensions
    {
        public static WeekScheduleResult ToWeekSchedule(this TeacherScheduleResult teacherSchedule)
        {
            var blocks = new List<ScheduleBlockResult>();
            
            // Get the maximum block count from the first day (assuming all days have same blocks)
            var maxBlocks = teacherSchedule.Days.Any()
                ? teacherSchedule.Days.Max(d => d.Blocks.Count)
                : 0;

            for (var blockIndex = 0; blockIndex < maxBlocks; blockIndex++)
            {
                var blockMetadata = new BlockMetadata(
                    blockIndex,
                    $"Period {blockIndex + 1}",
                    null, // BlockTimeRange not available in current config
                    null);

                ClassMetadata? monday = null;
                ClassMetadata? tuesday = null;
                ClassMetadata? wednesday = null;
                ClassMetadata? thursday = null;
                ClassMetadata? friday = null;

                foreach (var day in teacherSchedule.Days)
                {
                    if (blockIndex >= day.Blocks.Count) continue;

                    var block = day.Blocks[blockIndex];
                    if (block.IsFree) continue;

                    var classMetadata = new ClassMetadata(
                        block.ClassKey!,
                        block.ClassName!,
                        block.Department!,
                        block.Room);

                    switch (day.Day)
                    {
                        case DayOfWeek.Monday:
                            monday = classMetadata;
                            break;
                        case DayOfWeek.Tuesday:
                            tuesday = classMetadata;
                            break;
                        case DayOfWeek.Wednesday:
                            wednesday = classMetadata;
                            break;
                        case DayOfWeek.Thursday:
                            thursday = classMetadata;
                            break;
                        case DayOfWeek.Friday:
                            friday = classMetadata;
                            break;
                    }
                }

                blocks.Add(new ScheduleBlockResult(
                    blockMetadata,
                    monday,
                    tuesday,
                    wednesday,
                    thursday,
                    friday));
            }

            var teacher = new Teacher
            {
                Id = teacherSchedule.TeacherId,
                FullName = teacherSchedule.TeacherName
            };

            return new WeekScheduleResult(teacher, blocks);
        }
    }
}
