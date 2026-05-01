namespace SchedulePlanner.Core;

/// <summary>
/// Progress information for the scheduling solver, used for real-time reporting.
/// </summary>
/// <param name="Message">Human-readable progress message</param>
/// <param name="CurrentGap">Current gap between best solution and bound (if available)</param>
/// <param name="CurrentObjective">Current objective value (if available)</param>
/// <param name="BestObjective">Best objective value found so far</param>
/// <param name="IterationsCompleted">Number of solver iterations/completed</param>
/// <param name="Timestamp">UTC timestamp of this progress update</param>
/// <param name="Status">Current solver status</param>
public sealed record SolverProgress(
    string Message,
    double? CurrentGap,
    double? CurrentObjective,
    double? BestObjective,
    int IterationsCompleted,
    DateTime Timestamp,
    string? Status = null);

/// <summary>
/// Interface for reporting solver progress.
/// </summary>
public interface ISolverProgressReporter
{
    void ReportProgress(SolverProgress progress);
}
