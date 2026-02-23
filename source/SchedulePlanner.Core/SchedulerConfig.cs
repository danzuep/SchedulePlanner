namespace SchedulePlanner.Core;

using System;
using System.Collections.Generic;
using Google.OrTools.Sat;

public sealed record SchedulerConfig
{
    public static readonly string SectionName = "Scheduler";

    public IReadOnlyList<DayOfWeek> Days { get; init; } = new[]
    {
        DayOfWeek.Monday,
        DayOfWeek.Tuesday,
        DayOfWeek.Wednesday,
        DayOfWeek.Thursday,
        DayOfWeek.Friday
    };

    public int BlocksPerDay { get; init; } = 9;
    public int RoomChangePenalty { get; set; } = 3;
    public double SolverTimeLimitSeconds { get; init; } = 10.0;
    public List<Teacher> Teachers { get; init; } = new();
    public List<Class> Classes { get; init; } = new();
    public List<Department> Departments { get; init; } = new();
    public List<TeacherDepartment> TeacherDepartments { get; init; } = new();
}

public sealed record Teacher
{
    public int Id { get; init; }
    public string FullName { get; init; } = string.Empty;
    public string PreferredRoom { get; init; } = string.Empty;
    public int TargetLoadBlocks { get; init; } = 10;
}

public sealed record Class
{
    public string Key { get; init; } = string.Empty;
    public string Department { get; init; } = string.Empty;
    public string Name { get; init; } = string.Empty;
    public string PreferredRoom { get; init; } = string.Empty;
    public int WeeklyBlocks { get; init; } = 1;
}

public sealed record Department
{
    public string Key { get; init; } = string.Empty;
    public string Name { get; init; } = string.Empty;
}

public sealed record TeacherDepartment
{
    public string TeacherId { get; init; } = string.Empty;
    public string Department { get; init; } = string.Empty;
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