using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using Microsoft.Extensions.Options;
using SchedulePlanner.Core;

namespace SchedulePlanner.ImportExport.Excel
{
    public sealed class ExportService : IService
    {
        private readonly SchedulerOptions _config;
        private readonly ILogger<ExportService> _logger;

        public ExportService(IOptions<SchedulerOptions> config, ILogger<ExportService>? logger = null)
        {
            _config = config.Value;
            _logger = logger ?? NullLogger<ExportService>.Instance;
        }

        public async Task RunAsync(CancellationToken cancellationToken = default)
        {
            var importExportConfig = ImportExportOptions.Default;
            _ = await ExportAsync(_config, importExportConfig.FilePath).ConfigureAwait(false);
        }

        public Task<string> ExportAsync(SchedulerOptions config, string filePath, bool addTimestamp = false)
        {
            var writer = new ExcelSchedulerConfigWriter();
            var fullPath = writer.WriteSchedulerOptions(config, filePath, addTimestamp);
            _logger.LogInformation("Excel template written to {FilePath}", fullPath);
            return Task.FromResult(fullPath);
        }

        public Task<string> ExportAsync(ScheduleResult scheduleResult, string filePath, bool addTimestamp = false)
        {
            var writer = new ExcelSchedulerConfigWriter();
            var fullPath = writer.WriteScheduleResult(scheduleResult, filePath, addTimestamp);
            _logger.LogInformation("Excel template written to {FilePath}", fullPath);
            return Task.FromResult(fullPath);
        }

        public Task<string> ExportToICalAsync(ScheduleResult scheduleResult, string filePath, bool addTimestamp = false)
        {
            var icalContent = GenerateICalContent(scheduleResult);
            var fullPath = Path.Combine(Path.GetDirectoryName(filePath) ?? ".", Path.GetFileNameWithoutExtension(filePath) + (addTimestamp ? "_" + DateTime.Now.ToString("yyyyMMdd_HHmmss") : "") + ".ics");
            File.WriteAllText(fullPath, icalContent);
            _logger.LogInformation("iCal file written to {FilePath}", fullPath);
            return Task.FromResult(fullPath);
        }

        private string GenerateICalContent(ScheduleResult scheduleResult)
        {
            var sb = new System.Text.StringBuilder();
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

        public Task<string> ExportToCsvAsync(ScheduleResult scheduleResult, string filePath, bool addTimestamp = false)
        {
            var csvContent = GenerateCsvContent(scheduleResult);
            var fullPath = Path.Combine(Path.GetDirectoryName(filePath) ?? ".", Path.GetFileNameWithoutExtension(filePath) + (addTimestamp ? "_" + DateTime.Now.ToString("yyyyMMdd_HHmmss") : "") + ".csv");
            File.WriteAllText(fullPath, csvContent);
            _logger.LogInformation("CSV file written to {FilePath}", fullPath);
            return Task.FromResult(fullPath);
        }

        private string GenerateCsvContent(ScheduleResult scheduleResult)
        {
            var sb = new System.Text.StringBuilder();
            sb.AppendLine("Teacher,Day,Block,Class,Room");

            foreach (var teacherSchedule in scheduleResult.TeacherSchedules)
            {
                foreach (var daySchedule in teacherSchedule.Days)
                {
                    foreach (var block in daySchedule.Blocks)
                    {
                        if (!block.IsFree)
                        {
                            sb.AppendLine($"{teacherSchedule.TeacherName},{daySchedule.Day},{block.Block},{block.ClassName},{block.Room}");
                        }
                    }
                }
            }

            return sb.ToString();
        }
    }
}