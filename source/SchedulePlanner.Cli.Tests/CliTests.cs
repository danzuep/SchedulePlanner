namespace SchedulePlanner.Cli.Tests;

using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using SchedulePlanner.Cli;
using SchedulePlanner.Core;

public class CliTests
{
    [Test]
    public async Task Cli_AssemblyLoads()
    {
        var type = typeof(Program);
        await Assert.That(type).IsNotNull();
    }

    [Test]
    public async Task RunDemoScheduleAsync()
    {
        var host = Host.CreateDefaultBuilder()
            .InitialiseBuilderDefaults()
            .ConfigureServices((context, services) =>
            {
                Program.Initialise(context, services);
                services.AddScoped<IService<ScheduleResult>, SchedulingService>();
            })
            .Build();

        using var scope = host.Services.CreateScope();
        var logger = scope.ServiceProvider.GetRequiredService<ILogger<DemoScheduleRunner>>();
        var runner = new DemoScheduleRunner(logger);
        
        var result = await runner.RunAsync();
        
        await Assert.That(result).IsNotNull();
        await Assert.That(result.RunDuration).IsNotNull();
        
        var durationMs = result.RunDuration.Value.TotalMilliseconds;
        logger.LogInformation("Demo schedule run completed in {Duration}ms", durationMs);

        await Assert.That(result.HasSolution).IsTrue();
    }
}