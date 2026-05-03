namespace SchedulePlanner.ImportExport.Csv;

using System.Globalization;
using System.IO.Abstractions;
using System.Text;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using Microsoft.Extensions.Options;
using SchedulePlanner.Core;

public sealed class CsvScheduleResultExporter : IScheduleResultExporter
{
    private readonly ScheduleResultExportOptions _options;
    private readonly ILogger<CsvScheduleResultExporter> _logger;
    private readonly IFileSystem _fileSystem;

    public CsvScheduleResultExporter(
        IOptions<ScheduleResultExportOptions> options,
        ILogger<CsvScheduleResultExporter>? logger = null,
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
        _logger = logger ?? NullLogger<CsvScheduleResultExporter>.Instance;
        _fileSystem = fileSystem ?? new FileSystem();
    }

    public Task<string> ExportAsync()
    {
        var csvContent = GenerateCsvContent(_options.ScheduleResult);
        var timestamp = string.IsNullOrEmpty(_options.TimestampFormat) ? string.Empty :
            "_" + DateTimeOffset.Now.ToString(_options.TimestampFormat, CultureInfo.InvariantCulture);
        var fullPath = _fileSystem.Path.Combine(
            _fileSystem.Path.GetDirectoryName(_options.FilePath) ?? ".",
            _fileSystem.Path.GetFileNameWithoutExtension(_options.FilePath) + timestamp + ".csv");
        _fileSystem.File.WriteAllText(fullPath, csvContent);
        _logger.LogInformation("CSV file written to {FilePath}", fullPath);
        return Task.FromResult(fullPath);
    }

    private string GenerateCsvContent(ScheduleResult scheduleResult)
    {
        var sb = new StringBuilder();
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