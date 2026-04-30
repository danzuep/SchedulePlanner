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

See [Configuration.md](Configuration.md) for detailed configuration options and K-12 specific settings.

## Usage

See [Usage.md](Usage.md) for quick start, advanced usage, result structure, and export options.

## How It Works

1. **Validation & Assignment** — Config is validated; classes are mapped to teachers (via departments) and rooms (preferred room hierarchy).
2. **Hard Constraints** — Exact block counts, no teacher/room overlaps, preset exclusions.
3. **Soft Optimization** — Penalty variables minimize undesirable patterns (room changes, back-to-back classes, uneven distribution, etc.).
4. **Results** — Structured `ScheduleResult` with teacher timetables, class summaries, room change incidents, objective value, and solver stats.

Detailed explanations of each penalty and component are available in the full documentation.

## Technical Details

- Solver: Google OR-Tools CP-SAT
- .NET 8+ / C# 12
- Decision variables: Jagged boolean array `[assignment][day][block]` for variable blocks per day
- Synchronous core; async wrapper with `CancellationToken`

## Extensibility

Implement any of the interfaces (`IConfigValidator`, `IClassAssignmentBuilder`, `IConstraintBuilder`, `IOptimizationBuilder`, etc.) for custom behavior.

## Error Handling

Throws clear `InvalidOperationException` for configuration issues (missing data, over-assignment, negative penalties, etc.). Negative values are clamped with warnings.

---

## Completed K-12 Enhancements

The following K-12 features have been implemented:

### Core K-12 Support
- ✅ Add `ClassStream` model with size, proficiency level, and linked subjects
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
- ✅ Extend `Teacher` model with availability, part-time, certifications, max consecutive
- ✅ Add target load adherence penalty
- ✅ Add granular teacher preferences including early block restrictions

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

See [TODO.md](../TODO.md) for remaining enhancements.

### Additional Completed Features

- **Block Period Enhancements**: Support for common teacher planning blocks and team co-teaching, including extending the Class model for multiple teacher IDs, updating ClassAssignmentBuilder for multiple teachers, adding co-teaching constraints, common planning block penalties, and updating results to show co-teachers. Also, support for teachers sharing classrooms.

- **Usability & Operational Features**: Implementation of partial/incremental solving and "what-if" scenario support, including adding PreAssignedSlots to SchedulerOptions, modifying SchedulingService to fix pre-assigned variables, incremental solving with previous solution adjustments, what-if support with option cloning and partial reuse, and result comparison for scenarios.

- **General Improvements**: Breaking down advanced refactorings into smaller tasks, analyzing the project for architectural improvements including adding comprehensive unit tests for builders and validators, refactoring large methods in OptimizationBuilder, adding integration tests for end-to-end scenarios, implementing dependency injection for better testability, adding performance benchmarks, creating configuration schema validation, and adding logging for solver performance metrics.

- **Hybrid Schedules (Partial Completion)**: Extended SchedulerOptions with DayConfigs for per day blocks and merged blocks, updated SchedulingContext to handle variable blocks per day, modified decision variables to jagged array [day][block], updated all constraints and optimizations for variable blocks, added validation for day configs, and updated results to handle variable blocks per day.

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
