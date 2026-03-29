namespace SchedulePlanner.Core;

using System;
using System.Collections.Generic;
using Google.OrTools.Sat;
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
    public double SolverTimeLimitSeconds { get; set; } = 10.0;
    public List<Teacher> Teachers { get; set; } = new();
    public List<Class> Classes { get; set; } = new();
    public List<Department> Departments { get; set; } = new();
    public List<TeacherDepartment> TeacherDepartments { get; set; } = new();
}

public sealed record Teacher
{
    public string Id { get; set; } = string.Empty;
    public string FullName { get; set; } = string.Empty;
    public string PreferredRoom { get; set; } = string.Empty;
    public int TargetLoadBlocks { get; set; } = 10;
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

internal sealed record RoomChangePenalty(
    BoolVar Var,
    string TeacherId,
    DayOfWeek Day,
    int Block,
    string FromClassKey,
    string FromRoom,
    string ToClassKey,
    string ToRoom);