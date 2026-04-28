# SchedulePlanner.Core

**SchedulePlanner.Core** is a constraint-based school timetabling engine built with Google OR-Tools CP-SAT solver. It automatically generates optimal timetables by treating scheduling as a constraint satisfaction problem with configurable hard constraints and soft optimization objectives.

## Features

- Automatic generation of conflict-free timetables for teachers, classes, rooms, and time blocks
- Hard constraints: no double-booking, exact weekly block counts, preset block exclusions (e.g., lunch)
- Multi-objective optimization: minimizes room changes, schedule spread, uneven weekly distribution, class clustering, and inconsistent block times
- Flexible configuration for days, blocks, teachers, classes, and penalty weights
- Structured output: per-teacher and per-class schedules, penalty breakdowns, solver statistics
- Cancellation support and integrated logging

## Architecture

Clean separation of concerns:

```
SchedulingService (main orchestrator)
├── ConfigValidator
├── ClassAssignmentBuilder     (teacher-class-room mapping)
├── ConstraintBuilder          (hard rules)
├── OptimizationBuilder        (soft penalties)
├── ResultBuilder
└── ScheduleLogger
```

All major components are interface-based for easy testing and extension.

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

See **Usage** and **Dependency Injection** sections below for full examples.

## Configuration

Key properties in `SchedulerOptions`:

| Property                        | Description |
|---------------------------------|-------------|
| `Days`                          | List of scheduling days |
| `BlocksPerDay`                  | Number of time blocks per day |
| `Teachers`                      | List of teachers (with ID, name, preferred room, departments, target load) |
| `Classes`                       | List of classes (with Key, name, department, preferred room, WeeklyBlocks) |
| `PresetBlocks`                  | Fixed non-teaching slots (e.g., lunch) |
| Penalty weights (`RoomChangePenalty`, `ScheduleSpreadPenalty`, etc.) | Control optimization priorities |
| `SolverTimeLimitSeconds`        | Maximum solve time |

**Data Models** (Teacher, Class, PresetBlockConfig) are simple POCOs with required validation.

## How It Works

1. **Validation & Assignment** — Config is validated; classes are mapped to teachers (via departments) and rooms (preferred room hierarchy).
2. **Hard Constraints** — Exact block counts, no teacher/room overlaps, preset exclusions.
3. **Soft Optimization** — Penalty variables minimize undesirable patterns (room changes, back-to-back classes, uneven distribution, etc.).
4. **Results** — Structured `ScheduleResult` with teacher timetables, class summaries, room change incidents, objective value, and solver stats.

Detailed explanations of each penalty and component are available in the full documentation.

## Usage

Basic and DI examples remain as before (see original for code snippets).

Advanced usage: inject custom implementations of any builder interface for domain-specific logic.

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

## Technical Details

- Solver: Google OR-Tools CP-SAT
- .NET 8+ / C# 12
- Decision variables: 3D boolean array `[class, day, block]`
- Synchronous core; async wrapper with `CancellationToken`

## Extensibility

Implement any of the interfaces (`IConfigValidator`, `IClassAssignmentBuilder`, `IConstraintBuilder`, `IOptimizationBuilder`, etc.) for custom behavior.

## Error Handling

Throws clear `InvalidOperationException` for configuration issues (missing data, over-assignment, negative penalties, etc.). Negative values are clamped with warnings.

## Completed K-12 Enhancements

The following K-12 features have been implemented:

### Core K-12 Support
- ✅ Add `Stream` model with size, proficiency level, and linked subjects
- ✅ Extend `Class` to support multiple streams
- ✅ Update assignment logic for streams
- ✅ Add constraints for stream conflicts
- ✅ Add stream fragmentation penalty

### Block Period Enhancements
- ✅ Support merged blocks configuration
- ✅ Add A/B alternating schedules
- ✅ Add buffer constraints for merged blocks
- ✅ Add merged block consistency penalty

### Shared Classroom & Resource Improvements
- ✅ Extend `Room` model with capacity, equipment, shared status, buffer
- ✅ Enhance room assignment and constraints
- ✅ Add room utilization metrics
- ✅ Add shared room change penalty

### Teacher & Workload Enhancements
- ✅ Extend `Teacher` with availability, part-time, certifications, max consecutive
- ✅ Add target load adherence penalty
- ✅ Add early block restrictions

### Usability & Operational Features
- ✅ Add iCal and CSV export options
- ✅ Add per-stream schedule results
- ✅ Add student room transition penalty

### Testing & Data Generation
- ✅ Create SyntheticDataFactory with multiple scenarios
- ✅ Add comprehensive unit tests
- ✅ Move generators to tests with configurable builder and large school demo

### General Improvements
- ✅ Enhance ConfigValidator for validations
- ✅ Improve ScheduleLogger with statistics
- ✅ Document samples and templates

See TODO.md for remaining enhancements.

- ✅ Move TODOs into a separate checklist file



## Sample Extensions and Starter Templates

### Using Streams for Ability Grouping

```csharp
var options = new SchedulerOptions
{
    Classes = new List<Class>
    {
        new Class
        {
            Key = "Math101",
            Department = "Math",
            Streams = new List<Stream>
            {
                new Stream { Id = "Math101-Advanced", Size = 15, ProficiencyLevel = "Advanced", LinkedSubjects = new[] { "Math" } },
                new Stream { Id = "Math101-Basic", Size = 20, ProficiencyLevel = "Basic", LinkedSubjects = new[] { "Math" } }
            }
        }
    },
    Streams = new List<Stream> { /* global streams */ }
};
```

### Configuring Shared Rooms with Buffers

```csharp
var options = new SchedulerOptions
{
    Rooms = new List<Room>
    {
        new Room { Id = "Lab1", Capacity = 20, IsShared = true, SetupTimeBuffer = 1 }
    }
};
```

### Block Period Schedules

```csharp
var options = new SchedulerOptions
{
    ScheduleType = BlockScheduleType.ABAlternating,
    MergedBlocks = new List<MergedBlock>
    {
        new MergedBlock(new[] { 0, 1 }) // Double block
    }
};
```

### Synthetic Data Generation

Use `SyntheticDataFactory.GenerateStreamedScenario()` for quick testing.

### Export Options

```csharp
var exportService = new ExportService(options);
await exportService.ExportToICalAsync(scheduleResult, "schedule.ics");
await exportService.ExportToCsvAsync(scheduleResult, "schedule.csv");
```
