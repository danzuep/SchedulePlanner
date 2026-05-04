namespace SchedulePlanner.Cli.Tests;

using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using SchedulePlanner.Cli;

public class CliTests
{
    [Test]
    public async Task RunSmallDemoScheduleAsync()
    {
        using var host = Host.CreateDefaultBuilder()
            .ConfigureServices(services =>
            {
                services.AddDemoScheduleServices();
                services.AddScoped<DemoScheduleRunner>(provider =>
                    new DemoScheduleRunner(null, useSmallDemo: true)); // Use small demo for testing
            })
            .Build();

        using var scope = host.Services.CreateScope();
        var runner = scope.ServiceProvider.GetRequiredService<DemoScheduleRunner>();

        using var cts = new CancellationTokenSource(TimeSpan.FromSeconds(60)); // Limit test to 60 seconds

        var result = await runner.RunAsync(cts.Token);

        await Assert.That(result).IsNotNull();
        await Assert.That(result.HasSolution).IsTrue();
        await Assert.That(result.RunDuration).IsNotNull();
    }

    [Explicit("This test runs the full demo schedule, which can take a long time. Run explicitly when needed.")]
    [Test]
    public async Task RunDemoScheduleAsync()
    {
        using var host = Host.CreateDefaultBuilder()
            .InitialiseBuilderDefaults()
            .Build();

        using var scope = host.Services.CreateScope();
        var runner = scope.ServiceProvider.GetRequiredService<DemoScheduleRunner>();

        using var cts = new CancellationTokenSource(TimeSpan.FromMinutes(2));

        var result = await runner.RunAsync(cts.Token);

        await Assert.That(result).IsNotNull();
        await Assert.That(result.HasSolution).IsTrue();
        await Assert.That(result.RunDuration).IsNotNull();
    }
}