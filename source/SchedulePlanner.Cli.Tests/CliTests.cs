namespace SchedulePlanner.Cli.Tests;

using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using SchedulePlanner.Cli;

public class CliTests
{
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