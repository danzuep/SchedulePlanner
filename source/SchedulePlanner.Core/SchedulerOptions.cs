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
    public int RoomChangePenalty { get; set; } = 3;
    public int ScheduleSpreadPenalty { get; set; } = 2;
    public double SolverTimeLimitSeconds { get; set; } = 10.0;
    public List<Teacher> Teachers { get; set; } = new();
    public List<Class> Classes { get; set; } = new();
    public List<Department> Departments { get; set; } = new();
    public List<TeacherDepartment> TeacherDepartments { get; set; } = new();
    public List<PresetBlockConfig> PresetBlocks { get; set; } = new()
    {
        new PresetBlockConfig(6, "Lunch", MonTueWedThuFri),
        new PresetBlockConfig(2, "PACT", MonTueWed),
        new PresetBlockConfig(3, "Break", MonTueWed)
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
}

public sealed record Teacher
{
    public string Id { get; set; } = string.Empty;
    public string FullName { get; set; } = string.Empty;
    public string Email { get; set; } = string.Empty;
    public string PreferredRoom { get; set; } = string.Empty;
    public int TargetLoadBlocks { get; set; } = 10;
    public override string ToString() => $"{FullName} ({PreferredRoom})";
}

public sealed record Class
{
    public string Key { get; set; } = string.Empty;
    public string Department { get; set; } = string.Empty;
    public string Name { get; set; } = string.Empty;
    public string PreferredRoom { get; set; } = string.Empty;
    public int WeeklyBlocks { get; set; } = 1;
}

public sealed record Department
{
    public string Key { get; set; } = string.Empty;
    public string Name { get; set; } = string.Empty;
}

public sealed record TeacherDepartment
{
    public string TeacherId { get; set; } = string.Empty;
    public string Department { get; set; } = string.Empty;
}

public sealed record PresetBlockConfig(
    int Index,
    string Name,
    IReadOnlyList<DayOfWeek> Days);