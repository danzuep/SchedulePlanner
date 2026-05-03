namespace SchedulePlanner.ImportExport.Calendar;

using System.Globalization;
using System.IO.Abstractions;
using System.Text;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using Microsoft.Extensions.Options;
using SchedulePlanner.Core;
using SchedulePlanner.ImportExport;

public sealed class CalendarScheduleResultExporter : IScheduleResultExporter
{
    private readonly ScheduleResultExportOptions _options;
    private readonly ILogger<CalendarScheduleResultExporter> _logger;
    private readonly IFileSystem _fileSystem;

    public CalendarScheduleResultExporter(
        IOptions<ScheduleResultExportOptions> options,
        ILogger<CalendarScheduleResultExporter>? logger = null,
        IFileSystem? fileSystem = null)
    {
        _options = options?.Value ?? throw new ArgumentNullException(nameof(options));
        if (_options.ScheduleResult is null)
        {
            throw new ArgumentNullException(nameof(_options.ScheduleResult));
        }
        if (string.IsNullOrEmpty(_options.FilePath))
        {
            throw new ArgumentNullException(nameof(_options.FilePath));
        }
        _logger = logger ?? NullLogger<CalendarScheduleResultExporter>.Instance;
        _fileSystem = fileSystem ?? new FileSystem();
    }

    public Task<string> ExportAsync()
    {
        var icalContent = GenerateICalContent(_options.ScheduleResult);
        var timestamp = string.IsNullOrEmpty(_options.TimestampFormat) ? string.Empty :
            "_" + DateTimeOffset.Now.ToString(_options.TimestampFormat, CultureInfo.InvariantCulture);
        var fullPath = _fileSystem.Path.Combine(
            _fileSystem.Path.GetDirectoryName(_options.FilePath) ?? ".",
            _fileSystem.Path.GetFileNameWithoutExtension(_options.FilePath) + timestamp + ".ics");
        _fileSystem.File.WriteAllText(fullPath, icalContent);
        _logger.LogInformation("iCal file written to {FilePath}", fullPath);
        return Task.FromResult(fullPath);
    }

    private static string GenerateICalContent(ScheduleResult scheduleResult)
    {
        var sb = new StringBuilder();
        sb.AppendLine("BEGIN:VCALENDAR");
        sb.AppendLine("VERSION:2.0");
        sb.AppendLine("PRODID:-//SchedulePlanner//EN");

        var eventId = 1;
        foreach (var teacherSchedule in scheduleResult.TeacherSchedules)
        {
            foreach (var daySchedule in teacherSchedule.Days)
            {
                foreach (var block in daySchedule.Blocks)
                {
                    if (!block.IsFree)
                    {
                        var startTime = new DateTime(2026, 1, 1, 8, 0, 0).AddDays((int)daySchedule.Day - 1).AddMinutes(block.Block * 60); // Assume 1 hour blocks starting at 8am
                        var endTime = startTime.AddMinutes(60);
                        sb.AppendLine("BEGIN:VEVENT");
                        sb.AppendLine($"UID:{eventId}@scheduleplanner");
                        sb.AppendLine($"DTSTART:{startTime:yyyyMMddTHHmmss}");
                        sb.AppendLine($"DTEND:{endTime:yyyyMMddTHHmmss}");
                        sb.AppendLine($"SUMMARY:{block.ClassName} - {teacherSchedule.TeacherName}");
                        sb.AppendLine($"LOCATION:{block.Room}");
                        sb.AppendLine("END:VEVENT");
                        eventId++;
                    }
                }
            }
        }

        sb.AppendLine("END:VCALENDAR");
        return sb.ToString();
    }
}