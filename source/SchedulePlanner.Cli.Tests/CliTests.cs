namespace SchedulePlanner.Cli.Tests;

using System.Diagnostics;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using TUnit;
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
        var runner = new DemoScheduleRunner(
            scope.ServiceProvider.GetRequiredService<ILogger<DemoScheduleRunner>>());
        
        var result = await runner.RunAsync();
        
        await Assert.That(result).IsNotNull();
        await Assert.That(result.RunDuration).IsNotNull();
        
        var durationMs = result.RunDuration.Value.TotalMilliseconds;
        Console.WriteLine($"Demo schedule run completed in {durationMs:F0}ms");
        
        // For the large K12 scenario, it should take more than 1 second to run
        await Assert.That(durationMs).IsGreaterThan(1000.0);
    }
}