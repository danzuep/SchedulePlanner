# Usage

## Quick Start

```csharp
var options = new SchedulerOptions
{
    Days = new[] { DayOfWeek.Monday, DayOfWeek.Tuesday, DayOfWeek.Wednesday },
    BlocksPerDay = 8,
    Teachers = new List<Teacher> { /* ... */ },
    Classes = new List<Class> { /* ... */ },
    PresetBlocks = new List<PresetBlockConfig> { /* lunch, assemblies */ }
};

var service = new SchedulingService(Options.Create(options));
var result = await service.RunAsync();

if (result.HasSolution)
{
    // Use result.TeacherSchedules, result.Classes, etc.
}
```

## Advanced Usage

Inject custom implementations of any builder interface for domain-specific logic.

## Result Structure

`ScheduleResult` includes:
- `Status`, `HasSolution`, `ObjectiveValue`
- `TeacherSchedules` (day → block → class/room details)
- `Classes` (scheduled vs required blocks per class)
- `RoomChanges` and solver statistics

## Penalties Explained (Summary)

- **Room Change** — Teacher switching rooms between consecutive blocks
- **Schedule Spread** — Back-to-back classes (transition time)
- **Week Distribution** — Uneven daily teaching load
- **Class Day Clustering** — Multiple sessions of same class on one day
- **Class Block Consistency** — Same class at different times across days

Weights are configurable; all contribute to a single minimized objective.

## Export Options

```csharp
var exportService = new ExportService(options);
await exportService.ExportToICalAsync(scheduleResult, "schedule.ics");
await exportService.ExportToCsvAsync(scheduleResult, "schedule.csv");
```

## Synthetic Data Generation

Use `SyntheticDataFactory.GenerateStreamedScenario()` for quick testing.