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
            .InitialiseBuilderDefaults()
            .ConfigureServices(Initialise)
            .Build();

        var exportService = host.Services.GetRequiredService<ExportService>();
        await exportService.RunAsync();

        //Console.WriteLine("Press any key to exit...");
        //Console.ReadKey();
    }

    public static void Initialise(HostBuilderContext context, IServiceCollection services)
    {
        services.AddSingleton<ExportService>();
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
        MapCli(nameof(SchedulerConfig.BlocksPerDay));
        MapCli(nameof(SchedulerConfig.RoomChangePenalty));
        builder.AddCommandLine(args, switchMappings);
        return builder;

        void MapCli(string key)
        {
            var map = GetSwitchMapping(key);
            switchMappings.Add(map.Key, map.Value);
        }

        static KeyValuePair<string, string> GetSwitchMapping(string key) =>
            new($"--{key}", $"{SchedulerConfig.SectionName}:{key}");
    }
}