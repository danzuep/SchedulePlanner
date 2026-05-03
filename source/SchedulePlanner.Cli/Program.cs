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
        using var host = Host.CreateDefaultBuilder()
            .InitialiseBuilderDefaults(args)
            .Build();

        using var scope = host.Services.CreateScope();
        //var options = scope.ServiceProvider.GetRequiredService<SchedulerOptions>();
        var runDemo = args.Contains("--demo") || args.Contains("-d");
        if (runDemo)
        {
            var runner = scope.ServiceProvider.GetRequiredService<DemoScheduleRunner>();
            await runner.RunAsync();
        }
        else
        {
            var service = scope.ServiceProvider.GetRequiredService<ImportExportService>();
            await service.RunAsync();
        }
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
            services.AddDemoScheduleRunner(context.Configuration);
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
