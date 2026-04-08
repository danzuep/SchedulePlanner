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

            _constraintBuilder.AddSchedulingRules(context, variables, _config, cancellationToken);
            var penalties = _optimizationBuilder.AddRoomChangeOptimization(context, variables, _config, normalized.RoomChangePenalty, cancellationToken);
            var spreadPenalties = _optimizationBuilder.AddScheduleSpreadOptimization(context, variables, _config, normalized.ScheduleSpreadPenalty, cancellationToken);
            var weekDistPenalties = _optimizationBuilder.AddWeekDistributionOptimization(context, variables, _config, normalized.WeekDistributionPenalty, cancellationToken);
            var classDayClusteringPenalties = _optimizationBuilder.AddClassDayClusteringOptimization(context, variables, _config, normalized.ClassDayClusteringPenalty, cancellationToken);
            var classBlockConsistencyPenalties = _optimizationBuilder.AddClassBlockConsistencyOptimization(context, variables, _config, normalized.ClassBlockConsistencyPenalty, cancellationToken);

            // Combine all penalties for minimization
            var allPenaltyVars = penalties.Select(x => x.Var)
                .Concat(spreadPenalties.Select(x => x.Var))
                .Concat(weekDistPenalties.Select(x => x.Var))
                .Concat(classDayClusteringPenalties.Select(x => x.Var))
                .Concat(classBlockConsistencyPenalties.Select(x => x.Var))
                .ToArray();
            var allPenaltyWeights = Enumerable.Repeat(normalized.RoomChangePenalty, penalties.Count)
                .Concat(Enumerable.Repeat(normalized.ScheduleSpreadPenalty, spreadPenalties.Count))
                .Concat(Enumerable.Repeat(normalized.WeekDistributionPenalty, weekDistPenalties.Count))
                .Concat(Enumerable.Repeat(normalized.ClassDayClusteringPenalty, classDayClusteringPenalties.Count))
                .Concat(Enumerable.Repeat(normalized.ClassBlockConsistencyPenalty, classBlockConsistencyPenalties.Count))
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

            return new SchedulingContext(
                new CpModel(),
                classAssignments,
                teacherGroups,
                roomGroups,
                _config.Days.Count,
                _config.BlocksPerDay);
        }

        private ScheduleVariables CreateDecisionVariables(SchedulingContext context, CancellationToken cancellationToken)
        {
            var assignment = new BoolVar[context.ClassAssignments.Count, context.NumDays, context.BlocksPerDay];

            for (var cls = 0; cls < context.ClassAssignments.Count; ++cls)
            {
                cancellationToken.ThrowIfCancellationRequested();

                for (var day = 0; day < context.NumDays; ++day)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    for (var block = 0; block < context.BlocksPerDay; ++block)
                    {
                        cancellationToken.ThrowIfCancellationRequested();

                        assignment[cls, day, block] = context.Model.NewBoolVar(
                            $"assign_{context.ClassAssignments[cls].Config.Key}_day{day}_block{block}");
                    }
                }
            }

            return new ScheduleVariables(assignment);
        }

        private static CpSolver CreateSolver(double solverTimeLimitSeconds)
        {
            return new CpSolver
            {
                StringParameters = $"max_time_in_seconds:{solverTimeLimitSeconds}"
            };
        }
    }

    public sealed record ScheduleResult(
        string Status,
        bool HasSolution,
        double? ObjectiveValue,
        string SolverStatistics,
        IReadOnlyList<TeacherScheduleResult> TeacherSchedules,
        IReadOnlyList<ClassScheduleSummary> Classes,
        IReadOnlyList<RoomChangeResult> RoomChanges);

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
