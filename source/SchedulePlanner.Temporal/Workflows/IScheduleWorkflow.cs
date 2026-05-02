using SchedulePlanner.Core;
using Temporalio.Workflows;

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
