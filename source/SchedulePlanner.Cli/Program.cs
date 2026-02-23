using System.Diagnostics.CodeAnalysis;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using SchedulePlanner.Core;

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
            builder.AddCommandLineSwitchMappings((builder, switchMappings) =>
                builder.AddCommandLine(args, switchMappings), args);

        void InitialiseServices(HostBuilderContext context, IServiceCollection services)
        {
            services.AddSchedulingService(context.Configuration);
        }

        void InitialiseLogging(ILoggingBuilder builder) =>
            builder.AddSimpleConsole(options =>
            {
                options.SingleLine = false;
                options.TimestampFormat = "[HH:mm:ss] ";
            });
    }

    public static IConfigurationBuilder AddCommandLineSwitchMappings(this IConfigurationBuilder builder, Action<IConfigurationBuilder, IDictionary<string, string>> action, params string[] args)
    {
        if (builder == null)
        {
            throw new ArgumentNullException(nameof(builder));
        }
        if (action == null)
        {
            throw new ArgumentNullException(nameof(action));
        }
        if (args is { Length: > 0 })
        {
            var switchMappings = new Dictionary<string, string>()
        {
            { "-b", $"{SchedulerConfig.SectionName}:{nameof(SchedulerConfig.BlocksPerDay)}" },
            { "-p", $"{SchedulerConfig.SectionName}:{nameof(SchedulerConfig.RoomChangePenalty)}" }
        };
            action(builder, switchMappings);
        }
        return builder;
    }
}