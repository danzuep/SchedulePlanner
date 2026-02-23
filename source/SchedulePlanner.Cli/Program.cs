using System.Diagnostics.CodeAnalysis;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using SchedulePlanner;
using SchedulePlanner.Core;
using SchedulePlanner.Csv;

internal static class Program
{
    [ExcludeFromCodeCoverage]
    public static async Task Main(string[] args)
    {
        using var host = CreateConsoleHost(args);
        await host.RunAsync();

        Console.WriteLine("Press any key to exit...");
        Console.ReadKey();
    }

    public static IHost CreateConsoleHost(params string[] args)
    {
        return Host.CreateDefaultBuilder()
            .ConfigureAppConfiguration(InitialiseConfiguration)
            .ConfigureServices(InitialiseServices)
            .ConfigureLogging(InitialiseLogging)
            .UseConsoleLifetime()
            .Build();

        void InitialiseConfiguration(IConfigurationBuilder builder) =>
            builder.AddCommandLineSwitchMappings(args);

        void InitialiseServices(HostBuilderContext context, IServiceCollection services)
        {
            services.AddSchedulingService(context.Configuration);
            services.AddCsvSchedulerSources(context.Configuration);
            services.AddHostedService<Worker>();
        }

        void InitialiseLogging(ILoggingBuilder builder) =>
            builder.AddSimpleConsole(options =>
            {
                options.SingleLine = false;
                options.TimestampFormat = "[HH:mm:ss] ";
            });
    }

    public static IConfigurationBuilder AddCommandLineSwitchMappings(this IConfigurationBuilder builder, params string[] args)
    {
        if (builder == null)
        {
            throw new ArgumentNullException(nameof(builder));
        }
        var switchMappings = new Dictionary<string, string>()
        {
            { "--BlocksPerDay", $"{SchedulerConfig.SectionName}:{nameof(SchedulerConfig.BlocksPerDay)}" },
            { "--RoomChangePenalty", $"{SchedulerConfig.SectionName}:{nameof(SchedulerConfig.RoomChangePenalty)}" }
        };
        builder.AddCommandLine(args, switchMappings);
        return builder;
    }

    [ExcludeFromCodeCoverage]
    public class Worker : BackgroundService
    {
        private readonly IService _processExecutionService;

        public Worker(IService processExecutionService)
        {
            _processExecutionService = processExecutionService;
        }

        protected override async Task ExecuteAsync(CancellationToken cancellationToken)
        {
            await _processExecutionService.RunAsync(cancellationToken).ConfigureAwait(false);
        }
    }
}