using System.Text;
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

        public SchedulingService(IOptions<SchedulerOptions> config, ILogger<SchedulingService>? logger = null)
        {
            _config = config.Value;
            _logger = logger ?? NullLogger<SchedulingService>.Instance;
        }

        public Task<ScheduleResult> RunAsync(CancellationToken cancellationToken = default)
        {
            var normalized = ValidateAndNormalizeConfig();

            _logger.LogInformation(
                "Building timetable for {Days} days with {Blocks} blocks per day.",
                _config.Days.Count,
                _config.BlocksPerDay);

            var context = BuildSchedulingContext(cancellationToken);
            var variables = CreateDecisionVariables(context, cancellationToken);

            AddSchedulingRules(context, variables, cancellationToken);
            var penalties = AddRoomChangeOptimization(context, variables, normalized.RoomChangePenalty, cancellationToken);
            var spreadPenalties = AddScheduleSpreadOptimization(context, variables, normalized.ScheduleSpreadPenalty, cancellationToken);

            // Combine both penalties for minimization
            var allPenaltyVars = penalties.Select(x => x.Var)
                .Concat(spreadPenalties.Select(x => x.Var))
                .ToArray();
            var allPenaltyWeights = Enumerable.Repeat(normalized.RoomChangePenalty, penalties.Count)
                .Concat(Enumerable.Repeat(normalized.ScheduleSpreadPenalty, spreadPenalties.Count))
                .ToArray();

            context.Model.Minimize(
                LinearExpr.WeightedSum(allPenaltyVars.Cast<LinearExpr>(), allPenaltyWeights));

            var solver = CreateSolver(normalized.SolverTimeLimitSeconds);
            var status = solver.Solve(context.Model);

            var result = BuildResult(context, variables, penalties, solver, status);

            LogResult(result);

            return Task.FromResult(result);
        }

        private NormalizedSettings ValidateAndNormalizeConfig()
        {
            if (_config.Days == null || !_config.Days.Any())
            {
                throw new InvalidOperationException("You must specify at least one day in the Scheduler configuration.");
            }

            if (_config.BlocksPerDay <= 0)
            {
                throw new InvalidOperationException("BlocksPerDay must be greater than zero.");
            }

            if (_config.Classes == null || !_config.Classes.Any())
            {
                throw new InvalidOperationException("At least one class must be defined.");
            }

            if (_config.Teachers == null || !_config.Teachers.Any())
            {
                throw new InvalidOperationException("At least one teacher must be defined.");
            }

            if (_config.TeacherDepartments == null || !_config.TeacherDepartments.Any())
            {
                throw new InvalidOperationException("At least one department assignment is required.");
            }

            var solverTimeLimitSeconds = _config.SolverTimeLimitSeconds > 0
                ? _config.SolverTimeLimitSeconds
                : 10.0;

            if (_config.SolverTimeLimitSeconds <= 0)
            {
                _logger.LogWarning(
                    "SolverTimeLimitSeconds must be greater than zero; falling back to {DefaultTime} seconds.",
                    solverTimeLimitSeconds);
            }

            var roomChangePenalty = Math.Max(0, _config.RoomChangePenalty);

            if (_config.RoomChangePenalty < 0)
            {
                _logger.LogWarning("RoomChangePenalty must be non-negative; falling back to zero.");
            }

            var scheduleSpreadPenalty = Math.Max(0, _config.ScheduleSpreadPenalty);

            if (_config.ScheduleSpreadPenalty < 0)
            {
                _logger.LogWarning("ScheduleSpreadPenalty must be non-negative; falling back to zero.");
            }

            return new NormalizedSettings(solverTimeLimitSeconds, roomChangePenalty, scheduleSpreadPenalty);
        }

        private SchedulingContext BuildSchedulingContext(CancellationToken cancellationToken)
        {
            var classAssignments = BuildClassAssignments();
            var teacherGroups = BuildTeacherGroups(classAssignments);
            var roomGroups = BuildRoomGroups(classAssignments);

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

        private void AddSchedulingRules(
            SchedulingContext context,
            ScheduleVariables variables,
            CancellationToken cancellationToken)
        {
            RequireEachClassToBeScheduledForItsWeeklyBlocks(context, variables, cancellationToken);
            PreventTeachersFromBeingDoubleBooked(context, variables, cancellationToken);
            PreventRoomsFromBeingDoubleBooked(context, variables, cancellationToken);
            PreventSchedulingInDefaultBlocks(context, variables, cancellationToken);
        }

        private void PreventSchedulingInDefaultBlocks(
            SchedulingContext context,
            ScheduleVariables variables,
            CancellationToken cancellationToken)
        {
            if (_config.PresetBlocks == null || !_config.PresetBlocks.Any())
            {
                return;
            }

            foreach (var defaultBlock in _config.PresetBlocks)
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
                    for (var i = 0; i < _config.Days.Count; i++)
                    {
                        if (_config.Days[i] == day)
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

        private IReadOnlyList<RoomChangePenalty> AddRoomChangeOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
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
                                    _config.Days[day],
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

        private IReadOnlyList<ScheduleSpreadPenalty> AddScheduleSpreadOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
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
                                    _config.Days[day],
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

        private static CpSolver CreateSolver(double solverTimeLimitSeconds)
        {
            return new CpSolver
            {
                StringParameters = $"max_time_in_seconds:{solverTimeLimitSeconds}"
            };
        }

        private ScheduleResult BuildResult(
            SchedulingContext context,
            ScheduleVariables variables,
            IReadOnlyList<RoomChangePenalty> penalties,
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
                            else if (_config.PresetBlocks.FirstOrDefault(b => b.Index == blockIndex &&
                                b.Days.Contains(_config.Days[day])) is PresetBlockConfig presetBlock)
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

                        days.Add(new DayScheduleResult(_config.Days[day], blocks));
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
                solver.ResponseStats(),
                teacherSchedules,
                classSummaries,
                roomChanges);
        }

        private void LogResult(ScheduleResult result)
        {
            if (!result.HasSolution)
            {
                _logger.LogWarning(
                    "Solver finished with status {Status}; no timetable was produced.",
                    result.Status);

                _logger.LogInformation("Solver statistics: {Stats}", result.SolverStatistics);
                return;
            }

            _logger.LogInformation(
                "Timetable objective value (room-change penalties): {Objective}",
                result.ObjectiveValue);

            foreach (var teacher in result.TeacherSchedules)
            {
                _logger.LogInformation("Schedule for {Teacher} (ID {TeacherId}):", teacher.TeacherName, teacher.TeacherId);

                foreach (var day in teacher.Days)
                {
                    var builder = new StringBuilder();
                    builder.Append($"{day.Day,-9}: ");

                    foreach (var block in day.Blocks)
                    {
                        if (block.IsFree)
                        {
                            builder.Append("Free ");
                        }
                        else
                        {
                            builder.Append($"{block.ClassKey}({block.Room}) ");
                        }
                    }

                    _logger.LogInformation(builder.ToString());
                }
            }

            foreach (var classSummary in result.Classes)
            {
                _logger.LogInformation(
                    "Class {ClassId} scheduled for {Count}/{Required} blocks.",
                    classSummary.ClassKey,
                    classSummary.ScheduledBlocks,
                    classSummary.RequiredBlocks);
            }

            foreach (var roomChange in result.RoomChanges)
            {
                _logger.LogInformation(
                    "Penalty: {Teacher} changes from {FromRoom} ({FromClass}) to {ToRoom} ({ToClass}) on {Day} block {Block} -> {NextBlock}.",
                    roomChange.TeacherName,
                    roomChange.FromRoom,
                    roomChange.FromClassKey,
                    roomChange.ToRoom,
                    roomChange.ToClassKey,
                    roomChange.Day,
                    roomChange.FromBlock,
                    roomChange.ToBlock);
            }

            _logger.LogInformation("Solver statistics: {Stats}", result.SolverStatistics);
        }

        private IReadOnlyList<ClassAssignment> BuildClassAssignments()
        {
            var comparer = StringComparer.OrdinalIgnoreCase;

            var teachersById = _config.Teachers
                .ToDictionary(t => t.Id, t => t, comparer);

            var assignmentsByDepartment = _config.TeacherDepartments
                .Where(a => !string.IsNullOrWhiteSpace(a.Department))
                .GroupBy(a => a.Department, comparer)
                .ToDictionary(
                    g => g.Key,
                    g => g.Select(a => a.TeacherId)
                        .Where(id => !string.IsNullOrWhiteSpace(id))
                        .Distinct(comparer)
                        .ToList(),
                    comparer);

            var results = new List<ClassAssignment>(_config.Classes.Count);

            for (var index = 0; index < _config.Classes.Count; ++index)
            {
                var cls = _config.Classes[index];

                if (string.IsNullOrWhiteSpace(cls.Key))
                {
                    throw new InvalidOperationException($"Class at index {index} must define a Key.");
                }

                if (string.IsNullOrWhiteSpace(cls.Department))
                {
                    throw new InvalidOperationException($"Class {cls.Key} must specify a department.");
                }

                if (!assignmentsByDepartment.TryGetValue(cls.Department, out var teacherIds) || teacherIds.Count == 0)
                {
                    throw new InvalidOperationException(
                        $"No teacher assignment exists for department '{cls.Department}' required by class '{cls.Key}'.");
                }

                if (teacherIds.Count > 1)
                {
                    throw new InvalidOperationException(
                        $"Multiple teachers are assigned to department '{cls.Department}', so class '{cls.Key}' cannot resolve its teacher.");
                }

                var teacherId = teacherIds[0];
                if (!teachersById.TryGetValue(teacherId, out var teacher))
                {
                    throw new InvalidOperationException($"Class {cls.Key} references unknown teacher '{teacherId}'.");
                }

                var room = ResolveRoom(cls, teacher);
                if (string.IsNullOrWhiteSpace(room))
                {
                    throw new InvalidOperationException(
                        $"Unable to determine a room for class {cls.Key} taught by {teacher.FullName}.");
                }

                results.Add(new ClassAssignment(cls, teacher, index, room));
            }

            return results;
        }

        private IReadOnlyDictionary<string, TeacherGroup> BuildTeacherGroups(IReadOnlyList<ClassAssignment> classAssignments)
        {
            return classAssignments
                .GroupBy(entry => entry.Teacher.Id, StringComparer.OrdinalIgnoreCase)
                .ToDictionary(
                    g => g.Key,
                    g => new TeacherGroup(g.First().Teacher, g.ToList()),
                    StringComparer.OrdinalIgnoreCase);
        }

        private IReadOnlyDictionary<string, IReadOnlyList<ClassAssignment>> BuildRoomGroups(
            IReadOnlyList<ClassAssignment> classAssignments)
        {
            return classAssignments
                .GroupBy(entry => entry.Room, StringComparer.OrdinalIgnoreCase)
                .ToDictionary(
                    g => g.Key,
                    g => (IReadOnlyList<ClassAssignment>)g.ToList(),
                    StringComparer.OrdinalIgnoreCase);
        }

        private static string ResolveRoom(Class cls, Teacher teacher)
        {
            if (!string.IsNullOrWhiteSpace(teacher.PreferredRoom))
            {
                return teacher.PreferredRoom;
            }

            if (!string.IsNullOrWhiteSpace(cls.PreferredRoom))
            {
                return cls.PreferredRoom;
            }

            return string.Empty;
        }

        private sealed record NormalizedSettings(double SolverTimeLimitSeconds, int RoomChangePenalty, int ScheduleSpreadPenalty);

        private sealed record SchedulingContext(
            CpModel Model,
            IReadOnlyList<ClassAssignment> ClassAssignments,
            IReadOnlyDictionary<string, TeacherGroup> TeacherGroups,
            IReadOnlyDictionary<string, IReadOnlyList<ClassAssignment>> RoomGroups,
            int NumDays,
            int BlocksPerDay);

        private sealed record ScheduleVariables(BoolVar[,,] Assignment);

        private sealed record ClassAssignment(Class Config, Teacher Teacher, int Index, string Room);

        private sealed record TeacherGroup(Teacher Teacher, IReadOnlyList<ClassAssignment> Classes);
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