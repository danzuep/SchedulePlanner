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
    public async Task RunSmallDemoScheduleAsync()
    {
        using var host = Host.CreateDefaultBuilder()
            .ConfigureServices(services =>
            {
                services.AddDemoScheduleServices();
                services.AddScoped<DemoScheduleRunner>(provider =>
                    new DemoScheduleRunner(
                        provider.GetRequiredService<ILogger<DemoScheduleRunner>>(),
                        useSmallDemo: true,
                        progressTimeout: TimeSpan.FromSeconds(10),
                        disableExports: true));
                // Disable exports for testing
            })
            .Build();

        using var scope = host.Services.CreateScope();
        var runner = scope.ServiceProvider.GetRequiredService<DemoScheduleRunner>();

        using var cts = new CancellationTokenSource(TimeSpan.FromSeconds(60)); // Limit test to 60 seconds

        var progressUpdates = new List<SolverProgress>();
        var progress = new Progress<SolverProgress>(p => progressUpdates.Add(p));

        var result = await runner.RunAsync(cts.Token, progress);

        await Assert.That(result).IsNotNull();
        await Assert.That(result.HasSolution).IsTrue();
        await Assert.That(result.RunDuration).IsNotNull();
        await Assert.That(progressUpdates).IsNotEmpty();
    }

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
                        useUnsolvableDemo: true,
                        progressTimeout: TimeSpan.FromSeconds(1),
                        disableExports: true));
                // Use unsolvable demo with reasonable timeout
            })
            .Build();

        using var scope = host.Services.CreateScope();
        var runner = scope.ServiceProvider.GetRequiredService<DemoScheduleRunner>();

        using var cts = new CancellationTokenSource(TimeSpan.FromSeconds(30)); // Overall timeout

        var progressUpdates = new List<SolverProgress>();
        var progress = new Progress<SolverProgress>(p => progressUpdates.Add(p));

        var result = await runner.RunAsync(cts.Token, progress);

        await Assert.That(result).IsNotNull();
        // The unsolvable problem should result in no solution
        await Assert.That(result.HasSolution).IsFalse();
        // Progress updates should be captured during the solving attempt
        await Assert.That(progressUpdates).IsNotEmpty();
        // Verify the solver completed (either found infeasible or timed out)
        await Assert.That(result.RunDuration).IsNotNull();
        // The solver should complete within reasonable time (timeout should prevent runaway execution)
        await Assert.That(result.RunDuration.Value).IsLessThan(TimeSpan.FromSeconds(25));
    }

    //[Explicit("This test runs the full demo schedule, which can take a long time. Run explicitly when needed.")]
    [Test]
    public async Task RunDemoScheduleAsync()
    {
        using var host = Host.CreateDefaultBuilder()
            .InitialiseBuilderDefaults()
            //.ConfigureServices(services =>
            //{
            //    services.AddDemoScheduleServices();
            //    services.AddScoped<DemoScheduleRunner>(provider =>
            //        new DemoScheduleRunner(
            //            provider.GetRequiredService<ILogger<DemoScheduleRunner>>(),
            //            //progressTimeout: TimeSpan.FromSeconds(30),
            //            disableExports: true));
            //})
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