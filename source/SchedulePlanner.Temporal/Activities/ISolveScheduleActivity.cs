using System.Diagnostics;
using SchedulePlanner.Core;
using Temporalio.Activities;

namespace SchedulePlanner.Temporal.Activities;

/// <summary>
/// Activity for executing the CP-SAT solver with progress reporting and cancellation support.
/// </summary>
public interface ISolveScheduleActivity
{
    [Activity(nameof(SolveAsync))]
    Task<ScheduleResult> SolveAsync(SchedulerOptions config, string workflowId);
}
