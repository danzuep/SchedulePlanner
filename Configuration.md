# Configuration

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

## K-12 Specific Configuration

### Streams for Ability Grouping

```csharp
var options = new SchedulerOptions
{
    Classes = new List<Class>
    {
        new Class
        {
            Key = "Math101",
            Department = "Math",
            Streams = new List<ClassStream>
            {
                new ClassStream { Id = "Math101-Advanced", Size = 15, ProficiencyLevel = "Advanced", LinkedSubjects = new[] { "Math" } },
                new ClassStream { Id = "Math101-Basic", Size = 20, ProficiencyLevel = "Basic", LinkedSubjects = new[] { "Math" } }
            }
        }
    },
    Streams = new List<ClassStream> { /* global streams */ }
};
```

### Shared Rooms with Buffers

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

### Hybrid Schedules

```csharp
var options = new SchedulerOptions
{
    DayConfigs = new List<DayConfig>
    {
        new DayConfig(DayOfWeek.Monday, 8, new List<MergedBlock>()),
        new DayConfig(DayOfWeek.Tuesday, 6, new List<MergedBlock> { new MergedBlock(new[] { 0, 1 }) })
    }
};
```