namespace SchedulePlanner.Cli;

using System.Diagnostics.CodeAnalysis;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using SchedulePlanner.Core;
using SchedulePlanner.ImportExport;
using SchedulePlanner.ImportExport.Excel;

public static partial class Program
{
    [ExcludeFromCodeCoverage]
    public static async Task Main(string[] args)
    {
        // Support: dotnet run -- --demo (run demo schedule) or default to import-export
        if (args.Contains("--demo") || args.Contains("-d"))
        {
            await RunDemoScheduleAsync(args);
            return;
        }

        using var host = Host.CreateDefaultBuilder()
            .InitialiseBuilderDefaults()
            .ConfigureServices(Initialise)
            .Build();

        var service = host.Services.GetRequiredService<ImportExportService>();
        await service.RunAsync();
    }

    public static async Task RunDemoScheduleAsync(string[] args = null)
    {
        args ??= Array.Empty<string>();
        
        using var host = Host.CreateDefaultBuilder()
            .InitialiseBuilderDefaults()
            .ConfigureServices((context, services) =>
            {
                Initialise(context, services);
                services.AddScoped<IService<ScheduleResult>, SchedulingService>();
                services.AddTransient<ImportService>();
            })
            .Build();

        Console.WriteLine("Running demo schedule (Large K12 School)...");

        var options = DemoDataFactory.CreateLargeK12SchoolDemo();

        // Replace options in the service via a custom scope approach
        using var scope = host.Services.CreateScope();
        var logger = scope.ServiceProvider.GetRequiredService<ILogger<SchedulingService>>();
        var configValidator = scope.ServiceProvider.GetRequiredService<IConfigValidator>();
        var classAssignmentBuilder = scope.ServiceProvider.GetRequiredService<IClassAssignmentBuilder>();
        var constraintBuilder = scope.ServiceProvider.GetRequiredService<IConstraintBuilder>();
        var optimizationBuilder = scope.ServiceProvider.GetRequiredService<IOptimizationBuilder>();
        var resultBuilder = scope.ServiceProvider.GetRequiredService<IResultBuilder>();

        var service = new SchedulingService(
            Microsoft.Extensions.Options.Options.Create(options),
            logger,
            configValidator,
            classAssignmentBuilder,
            constraintBuilder,
            optimizationBuilder,
            resultBuilder,
            null);

        var result = await service.RunAsync();

        Console.WriteLine($"Solution found: {result.HasSolution}");
        if (result.HasSolution)
        {
            Console.WriteLine($"Teachers scheduled: {result.TeacherSchedules.Count}");
            Console.WriteLine($"Classes scheduled: {result.Classes.Count}");
            if (result.StreamSchedules?.Count > 0)
                Console.WriteLine($"Stream schedules: {result.StreamSchedules.Count}");

            var exportService = scope.ServiceProvider.GetRequiredService<ExportService>();
            var importExportConfig = ImportExportOptions.Default;
            var filePath = await exportService.ExportAsync(result, importExportConfig.FilePath, addTimestamp: true);
            Console.WriteLine($"Results exported to: {filePath}");

            var icalPath = await exportService.ExportToICalAsync(result, importExportConfig.FilePath, addTimestamp: true);
            Console.WriteLine($"iCal exported to: {icalPath}");

            var csvPath = await exportService.ExportToCsvAsync(result, importExportConfig.FilePath, addTimestamp: true);
            Console.WriteLine($"CSV exported to: {csvPath}");
        }
        else
        {
            Console.WriteLine($"No solution found. Status: {result.Status}");
        }
    }

    public static void Initialise(HostBuilderContext context, IServiceCollection services)
    {
        services.AddSingleton<ImportExportService>();
        services.AddSingleton<ExportService>();
        services.AddSingleton<ImportService>();

        // Register scheduling service dependencies for Cli demo runs
        services.AddSingleton<IConfigValidator, ConfigValidator>();
        services.AddSingleton<IClassAssignmentBuilder, ClassAssignmentBuilder>();
        services.AddSingleton<IConstraintBuilder, ConstraintBuilder>();
        services.AddSingleton<IOptimizationBuilder, OptimizationBuilder>();
        services.AddSingleton<IResultBuilder, ResultBuilder>();
        services.AddSingleton<IScheduleLogger, ScheduleLogger>();
    }

    public static IHostBuilder InitialiseBuilderDefaults(this IHostBuilder builder, params string[] args)
    {
        return builder
            .ConfigureAppConfiguration(InitialiseConfiguration)
            .ConfigureServices(InitialiseServices)
            .ConfigureLogging(InitialiseLogging)
            .UseConsoleLifetime();

        void InitialiseConfiguration(IConfigurationBuilder builder) =>
            builder.AddCommandLineSwitchMappings(args);

        void InitialiseServices(HostBuilderContext context, IServiceCollection services)
        {
            services.AddSchedulingService(context.Configuration);
            services.AddCsvSchedulerSources(context.Configuration);
            services.AddExcelSchedulerSources(context.Configuration);
        }

        void InitialiseLogging(ILoggingBuilder builder) =>
            builder.AddSimpleConsole(options =>
            {
                options.SingleLine = false;
                options.TimestampFormat = "[HH:mm:ss] ";
            });
    }

    private static IConfigurationBuilder AddCommandLineSwitchMappings(this IConfigurationBuilder builder, params string[] args)
    {
        var switchMappings = new Dictionary<string, string>();
        MapCli(nameof(SchedulerOptions.BlocksPerDay));
        MapCli(nameof(SchedulerOptions.RoomChangePenalty));
        builder.AddCommandLine(args, switchMappings);
        return builder;

        void MapCli(string key)
        {
            var map = GetSwitchMapping(key);
            switchMappings.Add(map.Key, map.Value);
        }

        static KeyValuePair<string, string> GetSwitchMapping(string key) =>
            new($"--{key}", $"{SchedulerOptions.SectionName}:{key}");
    }
}
