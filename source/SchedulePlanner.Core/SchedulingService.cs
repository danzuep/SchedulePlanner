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

    public sealed class SchedulingService : IService
    {
        public SchedulerOptions Config => _config;
        private readonly SchedulerOptions _config;
        private readonly ILogger<SchedulingService> _logger;

        public SchedulingService(IOptions<SchedulerOptions> config, ILogger<SchedulingService>? logger = null)
        {
            _config = config.Value;
            _logger = logger ?? NullLogger<SchedulingService>.Instance;
        }

        public Task RunAsync(CancellationToken cancellationToken = default)
        {
            var solverTimeLimitSeconds = ValidateConfig();
            var roomChangePenalty = Math.Max(0, _config.RoomChangePenalty);

            _logger.LogInformation("Building timetable for {Days} days with {Blocks} blocks per day.",
                _config.Days.Count, _config.BlocksPerDay);

            var classAssignments = BuildClassAssignments();

            var model = new CpModel();
            var numDays = _config.Days.Count;
            var blocksPerDay = _config.BlocksPerDay;
            var classCount = classAssignments.Count;

            var assignment = new BoolVar[classCount, numDays, blocksPerDay];
            for (var cls = 0; cls < classCount; ++cls)
            {
                cancellationToken.ThrowIfCancellationRequested();
                for (var day = 0; day < numDays; ++day)
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    for (var block = 0; block < blocksPerDay; ++block)
                    {
                        cancellationToken.ThrowIfCancellationRequested();
                        assignment[cls, day, block] = model.NewBoolVar(
                            $"assign_{classAssignments[cls].Config.Key}_day{day}_block{block}");
                    }
                }
            }

            foreach (var entry in classAssignments)
            {
                cancellationToken.ThrowIfCancellationRequested();
                var linear = new List<BoolVar>();
                for (var day = 0; day < numDays; ++day)
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    for (var block = 0; block < blocksPerDay; ++block)
                    {
                        cancellationToken.ThrowIfCancellationRequested();
                        linear.Add(assignment[entry.Index, day, block]);
                    }
                }

                if (entry.Config.WeeklyBlocks > numDays * blocksPerDay)
                {
                    throw new InvalidOperationException(
                        $"Class {entry.Config.Key} demands more blocks than available.");
                }

                model.Add(LinearExpr.Sum(linear) == entry.Config.WeeklyBlocks);
            }

            var teacherGroups = classAssignments
                .GroupBy(entry => entry.Teacher.Id, StringComparer.OrdinalIgnoreCase)
                .ToDictionary(
                    g => g.Key,
                    g => new TeacherGroup(g.First().Teacher, g.ToList()),
                    StringComparer.OrdinalIgnoreCase);

            foreach (var kvp in teacherGroups)
            {
                cancellationToken.ThrowIfCancellationRequested();
                var teacherAssignments = kvp.Value.Classes;
                for (var day = 0; day < numDays; ++day)
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    for (var block = 0; block < blocksPerDay; ++block)
                    {
                        cancellationToken.ThrowIfCancellationRequested();
                        var slots = teacherAssignments
                            .Select(entry => assignment[entry.Index, day, block])
                            .ToList();

                        if (slots.Count > 1)
                        {
                            model.AddAtMostOne(slots);
                        }
                    }
                }
            }

            var roomGroups = classAssignments
                .GroupBy(entry => entry.Room, StringComparer.OrdinalIgnoreCase)
                .ToDictionary(g => g.Key, g => g.ToList(), StringComparer.OrdinalIgnoreCase);

            foreach (var roomClasses in roomGroups.Values)
            {
                cancellationToken.ThrowIfCancellationRequested();
                for (var day = 0; day < numDays; ++day)
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    for (var block = 0; block < blocksPerDay; ++block)
                    {
                        cancellationToken.ThrowIfCancellationRequested();
                        var slots = roomClasses
                            .Select(entry => assignment[entry.Index, day, block])
                            .ToList();

                        if (slots.Count > 1)
                        {
                            model.AddAtMostOne(slots);
                        }
                    }
                }
            }

            var transitionPenalties = new List<RoomChangePenalty>();
            for (var day = 0; day < numDays; ++day)
            {
                cancellationToken.ThrowIfCancellationRequested();
                for (var block = 0; block < blocksPerDay - 1; ++block)
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    foreach (var teacherKvp in teacherGroups)
                    {
                        cancellationToken.ThrowIfCancellationRequested();
                        var teacherId = teacherKvp.Key;
                        var entries = teacherKvp.Value.Classes;
                        foreach (var current in entries)
                        {
                            cancellationToken.ThrowIfCancellationRequested();
                            foreach (var next in entries)
                            {
                                cancellationToken.ThrowIfCancellationRequested();
                                if (current.Room == next.Room)
                                {
                                    continue;
                                }

                                var penaltyVar = model.NewBoolVar(
                                    $"room_change_{teacherId}_day{day}_block{block}");

                                model.Add(penaltyVar <= assignment[current.Index, day, block]);
                                model.Add(penaltyVar <= assignment[next.Index, day, block + 1]);
                                model.Add(penaltyVar >= assignment[current.Index, day, block]
                                                     + assignment[next.Index, day, block + 1]
                                                     - 1);

                                transitionPenalties.Add(new RoomChangePenalty(
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

            var objVars = transitionPenalties.Select(p => p.Var).ToArray();
            var objCoeffs = Enumerable.Repeat(roomChangePenalty, objVars.Length).ToArray();
            model.Minimize(LinearExpr.WeightedSum(objVars.Cast<LinearExpr>(), objCoeffs));

            var solver = new CpSolver();
            solver.StringParameters = $"max_time_in_seconds:{solverTimeLimitSeconds}";
            var status = solver.Solve(model);

            if (status is CpSolverStatus.Optimal or CpSolverStatus.Feasible)
            {
                LogSolution(solver, assignment, classAssignments, teacherGroups, transitionPenalties);
            }
            else
            {
                _logger.LogWarning("Solver finished with status {Status}; no timetable was produced.", status);
            }

            _logger.LogInformation("Solver statistics: {Stats}", solver.ResponseStats());

            return Task.CompletedTask;
        }

        private void LogSolution(
            CpSolver solver,
            BoolVar[,,] assignment,
            IReadOnlyList<ClassAssignment> classes,
            IReadOnlyDictionary<string, TeacherGroup> teacherGroups,
            IReadOnlyList<RoomChangePenalty> penalties)
        {
            _logger.LogInformation("Timetable objective value (room-change penalties): {Objective}",
                solver.ObjectiveValue);

            foreach (var teacherEntry in teacherGroups)
            {
                var teacher = teacherEntry.Value.Teacher;
                _logger.LogInformation("Schedule for {Teacher} (ID {TeacherId}):", teacher.FullName, teacher.Id);

                for (var day = 0; day < _config.Days.Count; ++day)
                {
                    var builder = new StringBuilder();
                    builder.Append($"{_config.Days[day],-9}: ");
                    for (var block = 0; block < _config.BlocksPerDay; ++block)
                    {
                        var assigned = teacherEntry.Value.Classes.FirstOrDefault(entry =>
                            solver.BooleanValue(assignment[entry.Index, day, block]));

                        if (assigned is not null)
                        {
                            builder.Append($"{assigned.Config.Key}({assigned.Room}) ");
                        }
                        else
                        {
                            builder.Append("Free ");
                        }
                    }

                    _logger.LogInformation(builder.ToString());
                }
            }

            foreach (var entry in classes)
            {
                var count = 0;
                for (var day = 0; day < _config.Days.Count; ++day)
                {
                    for (var block = 0; block < _config.BlocksPerDay; ++block)
                    {
                        if (solver.BooleanValue(assignment[entry.Index, day, block]))
                        {
                            ++count;
                        }
                    }
                }

                _logger.LogInformation("Class {ClassId} scheduled for {Count}/{Required} blocks.",
                    entry.Config.Key, count, entry.Config.WeeklyBlocks);
            }

            foreach (var penalty in penalties)
            {
                if (!solver.BooleanValue(penalty.Var))
                {
                    continue;
                }

                var teacherName = teacherGroups.TryGetValue(penalty.TeacherId, out var teacherGroup)
                    ? teacherGroup.Teacher.FullName
                    : penalty.TeacherId;

                _logger.LogInformation(
                    "Penalty: {Teacher} changes from {FromRoom} ({FromClass}) to {ToRoom} ({ToClass}) on {Day} block {Block} -> {NextBlock}.",
                    teacherName,
                    penalty.FromRoom,
                    penalty.FromClassKey,
                    penalty.ToRoom,
                    penalty.ToClassKey,
                    penalty.Day,
                    penalty.Block,
                    penalty.Block + 1);
            }
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
                    throw new InvalidOperationException($"Unable to determine a room for class {cls.Key} taught by {teacher.FullName}.");
                }

                results.Add(new ClassAssignment(cls, teacher, index, room));
            }

            return results;
        }

        private static string ResolveRoom(Class cls, Teacher teacher)
        {
            if (!string.IsNullOrWhiteSpace(cls.PreferredRoom))
            {
                return cls.PreferredRoom;
            }

            if (!string.IsNullOrWhiteSpace(teacher.PreferredRoom))
            {
                return teacher.PreferredRoom;
            }

            return string.Empty;
        }

        private double ValidateConfig()
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

            var solverTimeLimit = _config.SolverTimeLimitSeconds > 0
                ? _config.SolverTimeLimitSeconds
                : 10.0;

            if (_config.SolverTimeLimitSeconds <= 0)
            {
                _logger.LogWarning(
                    "SolverTimeLimitSeconds must be greater than zero; falling back to {DefaultTime} seconds.",
                    solverTimeLimit);
            }

            if (_config.RoomChangePenalty < 0)
            {
                _logger.LogWarning(
                    "RoomChangePenalty must be non-negative; falling back to zero.");
            }

            return solverTimeLimit;
        }

        private sealed record ClassAssignment(Class Config, Teacher Teacher, int Index, string Room);

        private sealed record TeacherGroup(Teacher Teacher, IReadOnlyList<ClassAssignment> Classes);
    }
}