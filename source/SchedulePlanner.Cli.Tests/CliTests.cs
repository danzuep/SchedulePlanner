namespace SchedulePlanner.Cli.Tests;

using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using SchedulePlanner.Cli;
using SchedulePlanner.Core;

[NotInParallel]
public class CliTests
{
    [Test]
    public async Task ProgressTimeoutWorks()
    {
        using var host = Host.CreateDefaultBuilder()
            .ConfigureServices(services =>
            {
                services.AddDemoScheduleServices();
                services.AddScoped<DemoScheduleRunner>(provider =>
                    new DemoScheduleRunner(
                        provider.GetRequiredService<ILogger<DemoScheduleRunner>>(),
                        progressTimeout: TimeSpan.FromSeconds(1),
                        disableExports: true));
                // Use unsolvable demo with reasonable timeout
            })
            .Build();

        using var scope = host.Services.CreateScope();
        var runner = scope.ServiceProvider.GetRequiredService<DemoScheduleRunner>();

        using var cts = new CancellationTokenSource(TimeSpan.FromSeconds(30)); // Overall timeout

        var progressUpdates = new List<SolverProgress>();
        var progress = new Progress<SolverProgress>(progressUpdates.Add);

        var result = await runner.RunAsync(cts.Token, progress);

        await Assert.That(result).IsNotNull();
        // Verify the solver completed (either solved, infeasible, or timed out)
        await Assert.That(result.RunDuration).IsNotNull();
        // Progress updates should be captured during the solving attempt
        await Assert.That(progressUpdates).IsNotEmpty();
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

        var result = await runner.RunAsync();

        await Assert.That(result).IsNotNull();
        await Assert.That(result.HasSolution).IsTrue();
        await Assert.That(result.RunDuration).IsNotNull();
    }
}