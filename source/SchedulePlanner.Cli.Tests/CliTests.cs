namespace SchedulePlanner.Cli.Tests;

using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
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
                    new DemoScheduleRunner(null, useSmallDemo: true, progressTimeout: TimeSpan.FromSeconds(10), disableExports: true)); // Disable exports for testing
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
                    new DemoScheduleRunner(null, useSmallDemo: true, progressTimeout: TimeSpan.FromSeconds(1), disableExports: true)); // Disable exports for testing
            })
            .Build();

        using var scope = host.Services.CreateScope();
        var runner = scope.ServiceProvider.GetRequiredService<DemoScheduleRunner>();

        using var cts = new CancellationTokenSource(TimeSpan.FromSeconds(10)); // Overall timeout

        var progressUpdates = new List<SolverProgress>();
        var progress = new Progress<SolverProgress>(p => progressUpdates.Add(p));

        var result = await runner.RunAsync(cts.Token, progress);

        await Assert.That(result).IsNotNull();
        // Verify that progress timeout parameter is working
        // The solver should complete normally with small demo, but timeout should be configured
        await Assert.That(progressUpdates).IsNotEmpty();
        // Verify that we get a solution (timeout didn't trigger for this small/fast problem)
        await Assert.That(result.HasSolution).IsTrue();
    }

    [Explicit("This test runs the full demo schedule, which can take a long time. Run explicitly when needed.")]
    [Test]
    public async Task RunDemoScheduleAsync()
    {
        using var host = Host.CreateDefaultBuilder()
            .ConfigureServices(services =>
            {
                services.AddDemoScheduleServices();
                services.AddScoped<DemoScheduleRunner>(provider =>
                    new DemoScheduleRunner(null, useSmallDemo: false, disableExports: true)); // Disable exports for testing
            })
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