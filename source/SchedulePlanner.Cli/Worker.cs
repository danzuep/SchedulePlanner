using System.Diagnostics.CodeAnalysis;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using SchedulePlanner.Core;

[ExcludeFromCodeCoverage]
public class Worker : IHostedService, IDisposable
{
    private CancellationTokenSource? _cancellationTokenSource = null;
    private readonly IService _processExecutionService;
    private readonly IHostApplicationLifetime? _hostApplicationLifetime;
    private readonly ILogger _logger;

    public Worker(IService processExecutionService, IHostApplicationLifetime? hostApplicationLifetime = null, ILogger<Worker>? logger = null)
    {
        _processExecutionService = processExecutionService;
        _hostApplicationLifetime = hostApplicationLifetime;
        _logger = logger ?? NullLogger<Worker>.Instance;
    }

    public async Task StartAsync(CancellationToken cancellationToken = default)
    {
        _logger.LogInformation("Worker started at {time:o}", DateTimeOffset.Now);
        _cancellationTokenSource?.Dispose();
        _cancellationTokenSource = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
        await _processExecutionService.RunAsync(_cancellationTokenSource.Token).ConfigureAwait(false);
        await StopAsync(CancellationToken.None).ConfigureAwait(false);
    }

    public Task StopAsync(CancellationToken cancellationToken = default)
    {
        _logger.LogInformation("Worker finished at {time:o}", DateTimeOffset.Now);
        _hostApplicationLifetime?.StopApplication();
        return Task.CompletedTask;
    }

    public void Dispose()
    {
        _cancellationTokenSource?.Dispose();
    }
}
