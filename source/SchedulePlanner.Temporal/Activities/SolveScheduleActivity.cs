using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using Microsoft.Extensions.Options;
using SchedulePlanner.Core;
using Temporalio.Activities;

namespace SchedulePlanner.Temporal.Activities;

/// <summary>
/// Implementation of the scheduling solver activity.
/// </summary>
public sealed class SolveScheduleActivity : ISolveScheduleActivity, IDisposable
{
    private readonly ILogger<SolveScheduleActivity> _logger;
    private CancellationTokenSource? _cancellationTokenSource;
    private SolverProgress? _latestProgress; // accessed from multiple threads

    public SolveScheduleActivity(ILogger<SolveScheduleActivity> logger)
    {
        _logger = logger;
    }

    public async Task<ScheduleResult> SolveAsync(SchedulerOptions config, string workflowId)
    {
        _cancellationTokenSource = new CancellationTokenSource();
        var token = _cancellationTokenSource.Token;
        _latestProgress = null;

        _logger.LogInformation(
            "Starting solve activity for workflow {WorkflowId} with {Classes} classes, {Teachers} teachers, {Rooms} rooms",
            workflowId, config.Classes.Count, config.Teachers.Count, config.Rooms.Count);

        try
        {
            // Create a progress reporter that captures the latest progress from solver callbacks
            var progress = new Progress<Core.SolverProgress>(p => _latestProgress = p);

            var schedulingService = new SchedulingService(
                Options.Create(config),
                logger: NullLogger<SchedulingService>.Instance);

            // Start solver on a background thread
            var solverTask = Task.Run(() =>
                schedulingService.RunAsync(token, progress).GetAwaiter().GetResult(),
                token);

            // Periodically heartbeat while solver runs
            while (!solverTask.IsCompleted)
            {
                try
                {
                    ActivityExecutionContext.Current.Heartbeat(_latestProgress is null ? [new { message = "Solving..." }] : [_latestProgress]);
                }
                catch (Exception ex)
                {
                    _logger.LogWarning(ex, "Heartbeat failed");
                }

                // Wait a bit or until cancellation
                try
                {
                    await Task.Delay(TimeSpan.FromSeconds(5), token);
                }
                catch (OperationCanceledException) when (token.IsCancellationRequested)
                {
                    break;
                }
            }

            // Await final result (should be completed already)
            var result = await solverTask.ConfigureAwait(false);

            _logger.LogInformation("Solve activity completed for workflow {WorkflowId}. Status: {Status}, Objective: {Objective}",
                workflowId, result.Status, result.ObjectiveValue);

            return result;
        }
        catch (OperationCanceledException) when (token.IsCancellationRequested)
        {
            _logger.LogWarning("Solve activity cancelled for workflow {WorkflowId}", workflowId);
            throw;
        }
        catch (Exception ex)
        {
            _logger.LogError(ex, "Solve activity failed for workflow {WorkflowId}", workflowId);
            throw;
        }
    }

    public void Dispose()
    {
        _cancellationTokenSource?.Cancel();
        _cancellationTokenSource?.Dispose();
    }
}
