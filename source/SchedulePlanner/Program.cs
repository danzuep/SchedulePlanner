using System.Text;
using Google.OrTools.Sat;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;

namespace SchedulePlanner
{
    internal static class Program
    {
        public static async Task Main(string[] args)
        {
            using var host = Host.CreateDefaultBuilder(args)
                .ConfigureHostConfiguration(config =>
                {
                    config.AddEnvironmentVariables(prefix: "SCHED_");
                })
                .ConfigureAppConfiguration((context, config) =>
                {
                    config.AddCommandLine(args);
                    config.SetBasePath(Directory.GetCurrentDirectory());
                    config.AddJsonFile("appsettings.json");
                })
                .ConfigureServices((context, services) =>
                {
                    services.Configure<SchedulerConfig>(context.Configuration.GetSection("Scheduler"));
                    services.AddSingleton<SchedulingService>();
                })
                .ConfigureLogging(logging =>
                {
                    logging.ClearProviders();
                    logging.AddSimpleConsole(options =>
                    {
                        options.SingleLine = false;
                        options.TimestampFormat = "[HH:mm:ss] ";
                    });
                })
                .Build();

            var scheduler = host.Services.GetRequiredService<SchedulingService>();
            await scheduler.RunAsync();

            Console.WriteLine("Press any key to exit...");
            Console.ReadKey();
        }
    }

    public sealed class SchedulingService
    {
        private readonly ILogger<SchedulingService> _logger;
        private readonly SchedulerConfig _config;

        public SchedulingService(ILogger<SchedulingService> logger, IOptions<SchedulerConfig> config)
        {
            _logger = logger;
            _config = config.Value;
        }

        public Task RunAsync()
        {
            Solve();
            return Task.CompletedTask;
        }

        private void Solve()
        {
            ValidateConfig();

            _logger.LogInformation("Building timetable for {Days} days with {Blocks} blocks per day.",
                _config.Days.Count, _config.BlocksPerDay);

            var classes = _config.Classes
                .Select((cls, idx) => new ClassEntry(cls, idx))
                .ToList();

            var model = new CpModel();
            var numDays = _config.Days.Count;
            var blocksPerDay = _config.BlocksPerDay;

            var assignment = new BoolVar[classes.Count, numDays, blocksPerDay];
            for (var cls = 0; cls < classes.Count; ++cls)
            for (var day = 0; day < numDays; ++day)
            for (var block = 0; block < blocksPerDay; ++block)
            {
                assignment[cls, day, block] = model.NewBoolVar(
                    $"assign_{classes[cls].Config.Id}_day{day}_block{block}");
            }

            foreach (var entry in classes)
            {
                var linear = new List<BoolVar>();
                for (var day = 0; day < numDays; ++day)
                for (var block = 0; block < blocksPerDay; ++block)
                {
                    linear.Add(assignment[entry.Index, day, block]);
                }

                if (entry.Config.WeeklyBlocks > numDays * blocksPerDay)
                {
                    throw new InvalidOperationException(
                        $"Class {entry.Config.Id} demands more blocks than available.");
                }

                model.Add(LinearExpr.Sum(linear) == entry.Config.WeeklyBlocks);
            }

            var teacherGroups = classes
                .GroupBy(c => c.Config.Teacher)
                .ToDictionary(g => g.Key, g => g.ToList());

            foreach (var teacherClasses in teacherGroups.Values)
            {
                for (var day = 0; day < numDays; ++day)
                for (var block = 0; block < blocksPerDay; ++block)
                {
                    var slots = teacherClasses
                        .Select(entry => assignment[entry.Index, day, block])
                        .ToList();

                    if (slots.Count > 1)
                    {
                        model.AddAtMostOne(slots);
                    }
                }
            }

            var roomGroups = classes
                .GroupBy(c => c.Config.Room)
                .ToDictionary(g => g.Key, g => g.ToList());

            foreach (var roomClasses in roomGroups.Values)
            {
                for (var day = 0; day < numDays; ++day)
                for (var block = 0; block < blocksPerDay; ++block)
                {
                    var slots = roomClasses
                        .Select(entry => assignment[entry.Index, day, block])
                        .ToList();

                    if (slots.Count > 1)
                    {
                        model.AddAtMostOne(slots);
                    }
                }
            }

            var transitionPenalties = new List<RoomChangePenalty>();
            for (var day = 0; day < numDays; ++day)
            for (var block = 0; block < blocksPerDay - 1; ++block)
            {
                foreach (var teacher in teacherGroups)
                {
                    var entries = teacher.Value;
                    foreach (var current in entries)
                    foreach (var next in entries)
                    {
                        if (current.Config.Room == next.Config.Room)
                        {
                            continue;
                        }

                        var penaltyVar = model.NewBoolVar(
                            $"room_change_{teacher.Key}_day{day}_block{block}");

                        model.Add(penaltyVar <= assignment[current.Index, day, block]);
                        model.Add(penaltyVar <= assignment[next.Index, day, block + 1]);
                        model.Add(penaltyVar >= assignment[current.Index, day, block]
                                             + assignment[next.Index, day, block + 1]
                                             - 1);

                        transitionPenalties.Add(new RoomChangePenalty(
                            penaltyVar,
                            teacher.Key,
                            _config.Days[day],
                            block,
                            current.Config.Id,
                            current.Config.Room,
                            next.Config.Id,
                            next.Config.Room));
                    }
                }
            }

            var objVars = transitionPenalties.Select(p => p.Var).ToList();
            var objCoeffs = Enumerable.Repeat(_config.RoomChangePenalty, objVars.Count).ToList();
            model.Minimize(LinearExpr.WeightedSum(objVars.Cast<LinearExpr>(), objCoeffs));

            var solver = new CpSolver();
            solver.StringParameters = $"max_time_in_seconds:{_config.Solver.TimeLimitSeconds}";
            var status = solver.Solve(model);

            if (status is CpSolverStatus.Optimal or CpSolverStatus.Feasible)
            {
                LogSolution(solver, assignment, classes, teacherGroups, transitionPenalties);
            }
            else
            {
                _logger.LogWarning("Solver finished with status {Status}; no timetable was produced.", status);
            }

            _logger.LogInformation("Solver statistics: {Stats}", solver.ResponseStats());
        }

        private void LogSolution(
            CpSolver solver,
            BoolVar[,,] assignment,
            IReadOnlyList<ClassEntry> classes,
            IReadOnlyDictionary<string, List<ClassEntry>> teacherGroups,
            IReadOnlyList<RoomChangePenalty> penalties)
        {
            _logger.LogInformation("Timetable objective value (room-change penalties): {Objective}",
                solver.ObjectiveValue);

            foreach (var teacher in teacherGroups)
            {
                _logger.LogInformation("Schedule for {Teacher}:", teacher.Key);
                for (var day = 0; day < _config.Days.Count; ++day)
                {
                    var builder = new StringBuilder();
                    builder.Append($"{_config.Days[day],-9}: ");
                    for (var block = 0; block < _config.BlocksPerDay; ++block)
                    {
                        var assigned = teacher.Value.FirstOrDefault(entry =>
                            solver.BooleanValue(assignment[entry.Index, day, block]));

                        if (assigned is not null)
                        {
                            builder.Append($"{assigned.Config.Id}({assigned.Config.Room}) ");
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
                for (var block = 0; block < _config.BlocksPerDay; ++block)
                {
                    if (solver.BooleanValue(assignment[entry.Index, day, block]))
                    {
                        ++count;
                    }
                }

                _logger.LogInformation("Class {ClassId} scheduled for {Count}/{Required} blocks.",
                    entry.Config.Id, count, entry.Config.WeeklyBlocks);
            }

            foreach (var penalty in penalties)
            {
                if (solver.BooleanValue(penalty.Var))
                {
                    _logger.LogInformation(
                        "Penalty: {Teacher} changes from {FromRoom} ({FromClass}) to {ToRoom} ({ToClass}) on {Day} block {Block} -> {NextBlock}.",
                        penalty.Teacher,
                        penalty.FromRoom,
                        penalty.FromClass,
                        penalty.ToRoom,
                        penalty.ToClass,
                        penalty.Day,
                        penalty.Block,
                        penalty.Block + 1);
                }
            }
        }

        private void ValidateConfig()
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

            var teacherSet = new HashSet<string>(_config.Teachers.Select(t => t.Name));
            foreach (var cls in _config.Classes)
            {
                if (!teacherSet.Contains(cls.Teacher))
                {
                    throw new InvalidOperationException($"Class {cls.Id} references unknown teacher {cls.Teacher}.");
                }
            }

            if (_config.RoomChangePenalty < 0)
            {
                _config.RoomChangePenalty = 0;
            }

            if (_config.Solver == null)
            {
                _config.Solver = new SolverConfig();
            }

            if (_config.Solver.TimeLimitSeconds <= 0)
            {
                _config.Solver = _config.Solver with { TimeLimitSeconds = 10.0 };
            }
        }
    }

    public sealed record SchedulerConfig
    {
        public List<string> Days { get; init; } = new();
        public int BlocksPerDay { get; init; } = 9;
        public int RoomChangePenalty { get; set; } = 5;
        public SolverConfig Solver { get; set; } = new();
        public List<TeacherConfig> Teachers { get; init; } = new();
        public List<ClassConfig> Classes { get; init; } = new();
    }

    public sealed record SolverConfig
    {
        public double TimeLimitSeconds { get; init; } = 10.0;
    }

    public sealed record TeacherConfig(string Name);

    public sealed record ClassConfig
    {
        public string Id { get; init; } = string.Empty;
        public string Teacher { get; init; } = string.Empty;
        public string Room { get; init; } = string.Empty;
        public int WeeklyBlocks { get; init; }
    }

    internal sealed record ClassEntry(ClassConfig Config, int Index);

    internal sealed record RoomChangePenalty(
        BoolVar Var,
        string Teacher,
        string Day,
        int Block,
        string FromClass,
        string FromRoom,
        string ToClass,
        string ToRoom);
}