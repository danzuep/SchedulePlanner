namespace SchedulePlanner.Core;

using System;
using System.Collections.Generic;
using Microsoft.Extensions.Options;

public sealed record SchedulerOptions : IOptions<SchedulerOptions>
{
    public SchedulerOptions Value => this;

    public static readonly string SectionName = "Scheduler";

    public static readonly string SettingsName = "Settings";

    public IReadOnlyList<DayOfWeek> Days { get; set; } = new[]
    {
        DayOfWeek.Monday,
        DayOfWeek.Tuesday,
        DayOfWeek.Wednesday,
        DayOfWeek.Thursday,
        DayOfWeek.Friday
    };

    public int BlocksPerDay { get; set; } = 9;
    public List<MergedBlock> MergedBlocks { get; set; } = new();
    public BlockScheduleType ScheduleType { get; set; } = BlockScheduleType.Traditional;
    public List<DayConfig> DayConfigs { get; set; } = new();
    public int RoomChangePenalty { get; set; } = 3;
    public int ScheduleSpreadPenalty { get; set; } = 2;
    public int WeekDistributionPenalty { get; set; } = 1;
    public int ClassDayClusteringPenalty { get; set; } = 1;
    public int ClassBlockConsistencyPenalty { get; set; } = 1;
    public int StreamFragmentationPenalty { get; set; } = 1;
    public int SharedRoomChangePenalty { get; set; } = 5;
    public int TargetLoadAdherencePenalty { get; set; } = 2;
    public int StudentRoomTransitionPenalty { get; set; } = 2;
    public int FreeTimePenalty { get; set; } = 1;
    public int MergedBlockConsistencyPenalty { get; set; } = 1;
    public double SolverTimeLimitSeconds { get; set; } = 30.0;
    public List<Teacher> Teachers { get; set; } = new();
    public List<Class> Classes { get; set; } = new();
    public List<Stream> Streams { get; set; } = new();
    public List<Room> Rooms { get; set; } = new();
    public List<PreAssignedSlot> PreAssignedSlots { get; set; } = new();
    public ScheduleResult? PreviousScheduleResult { get; set; }
    public List<PresetBlockConfig> PresetBlocks { get; set; } = new()
    {
        new PresetBlockConfig(6, "Lunch", MonTueWedThuFri),
        new PresetBlockConfig(2, "PACT", MonTueWed),
        //new PresetBlockConfig(2, "Assembly", ThuFri),
        //new PresetBlockConfig(3, "Break", MonTueWedThuFri),
        new PresetBlockConfig(3, "Break", MonTueWed),
        new PresetBlockConfig(0, "Free", [DayOfWeek.Friday])
    };
    private static readonly IReadOnlyList<DayOfWeek> MonTueWedThuFri =
    [
        DayOfWeek.Monday,
        DayOfWeek.Tuesday,
        DayOfWeek.Wednesday,
        DayOfWeek.Thursday,
        DayOfWeek.Friday
    ];
    private static readonly IReadOnlyList<DayOfWeek> MonTueWed =
    [
        DayOfWeek.Monday,
        DayOfWeek.Tuesday,
        DayOfWeek.Wednesday
    ];
    private static readonly IReadOnlyList<DayOfWeek> ThuFri =
    [
        DayOfWeek.Thursday,
        DayOfWeek.Friday
    ];
}

public enum BlockScheduleType
{
    Traditional,
    ABAlternating,
    Rotating
}

public sealed record DayConfig(DayOfWeek Day, int BlocksPerDay, IReadOnlyList<MergedBlock> MergedBlocks);

public sealed record PreAssignedSlot(int AssignmentIndex, int Day, int Block);

public sealed record Room
{
    public string Id { get; set; } = string.Empty;
    public int Capacity { get; set; } = 30;
    public string EquipmentType { get; set; } = string.Empty;
    public bool IsShared { get; set; } = false;
    public int SetupTimeBuffer { get; set; } = 0;
}

public sealed record Teacher
{
    public string Id { get; set; } = string.Empty;
    public string FullName { get; set; } = string.Empty;
    public string Email { get; set; } = string.Empty;
    public string PreferredRoom { get; set; } = string.Empty;
    public int TargetLoadBlocks { get; set; } = 20;
    public IReadOnlyList<string> Departments { get; set; } = new List<string>();
    public IReadOnlyList<DayOfWeek> AvailabilityPatterns { get; set; } = new List<DayOfWeek>();
    public bool IsPartTime { get; set; } = false;
    public IReadOnlyList<string> Certifications { get; set; } = new List<string>();
    public int MaxConsecutiveBlocks { get; set; } = 5;
    public int NoEarlyBlocksBefore { get; set; } = 0;
    public bool PrefersCoTeaching { get; set; } = false;
    public override string ToString() => $"{FullName} ({PreferredRoom})";
}

public sealed record Class
{
    public string Key { get; set; } = string.Empty;
    public string Department { get; set; } = string.Empty;
    public string Name { get; set; } = string.Empty;
    public string PreferredRoom { get; set; } = string.Empty;
    public int WeeklyBlocks { get; set; } = 4;
    public List<Stream> Streams { get; set; } = new();
    public List<string> TeacherIds { get; set; } = new();
}

public sealed record Stream
{
    public string Id { get; set; } = string.Empty;
    public int Size { get; set; }
    public string ProficiencyLevel { get; set; } = string.Empty;
    public IReadOnlyList<string> LinkedSubjects { get; set; } = new List<string>();
}

public sealed record MergedBlock(IReadOnlyList<int> BlockIndices);

public sealed record PresetBlockConfig(
    int Index,
    string Name,
    IReadOnlyList<DayOfWeek> Days);