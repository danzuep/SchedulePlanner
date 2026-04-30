using System.Diagnostics;
using System.Diagnostics.Metrics;

namespace SchedulePlanner.Core
{
    public static class SchedulerDiagnostics
    {
        public static readonly ActivitySource ActivitySource = new("SchedulePlanner");
        public static readonly Meter Meter = new("SchedulePlanner", "1.0.0");
        public static readonly Counter<int> SchedulerRuns = Meter.CreateCounter<int>("scheduler.runs", description: "Number of scheduling runs");
        public static readonly Histogram<double> SchedulerDuration = Meter.CreateHistogram<double>("scheduler.duration", unit: "ms", description: "Scheduling duration in milliseconds");
    }
}
