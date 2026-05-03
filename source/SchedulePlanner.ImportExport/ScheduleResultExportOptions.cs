namespace SchedulePlanner.ImportExport;

using Microsoft.Extensions.Options;
using SchedulePlanner.Core;

public sealed record ScheduleResultExportOptions : IOptions<ScheduleResultExportOptions>
{
    public static readonly string SectionName = "Export";
    public ScheduleResultExportOptions Value => this;

    public string FilePath { get; set; } = null!;
    public string? TimestampFormat { get; set; } = "yyyyMMdd_HHmmss";
    public ScheduleResult ScheduleResult { get; init; } = null!;
}
