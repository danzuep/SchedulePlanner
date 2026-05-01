using System;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Extensions.Logging;
using Temporalio.Workflows;
using Temporalio;
using Temporalio.Common;
using SchedulePlanner.Core;
using SchedulePlanner.Temporal.Activities;

namespace SchedulePlanner.Temporal.Workflows;

/// <summary>
/// Temporal workflow for reliable long-running scheduling with progress tracking,
/// cancellation support, and incremental re-solving capabilities.
/// </summary>
[Workflow]
public interface IScheduleWorkflow
{
    [WorkflowRun]
    Task<ScheduleResult> RunScheduleAsync(SchedulerOptions config, string? workflowId = null);
}

/// <summary>
/// Implementation of the schedule workflow.
/// </summary>
[Workflow]
public sealed class ScheduleWorkflow : IScheduleWorkflow
{
    [WorkflowRun]
    public async Task<ScheduleResult> RunScheduleAsync(SchedulerOptions config, string? workflowId = null)
    {
        var token = Workflow.CancellationToken;
        var logger = Workflow.Logger;
        logger.LogInformation("Starting schedule workflow. Config: {Days} days, {Blocks} blocks per day, {Classes} classes",
            config.Days.Count, config.BlocksPerDay, config.Classes.Count);

        // Execute the solver activity with retry policy
        var retryPolicy = new RetryPolicy
        {
            InitialInterval = TimeSpan.FromSeconds(1),
            MaximumInterval = TimeSpan.FromSeconds(30),
            MaximumAttempts = 3,
            BackoffCoefficient = 2.0F
        };

        var result = await Workflow.ExecuteActivityAsync(
            (ISolveScheduleActivity act) => act.SolveAsync(config, Workflow.Info.RunId),
            new ActivityOptions
            {
                ScheduleToCloseTimeout = TimeSpan.FromSeconds(config.SolverTimeLimitSeconds + 60),
                StartToCloseTimeout = TimeSpan.FromSeconds(config.SolverTimeLimitSeconds + 30),
                HeartbeatTimeout = TimeSpan.FromSeconds(10),
                RetryPolicy = retryPolicy
            });

        logger.LogInformation("Schedule workflow completed. Status: {Status}, HasSolution: {HasSolution}",
            result.Status, result.HasSolution);

        return result;
    }
}
