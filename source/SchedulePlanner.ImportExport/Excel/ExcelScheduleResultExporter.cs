namespace SchedulePlanner.ImportExport.Excel;

using System.IO.Abstractions;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using Microsoft.Extensions.Options;

public sealed class ExcelScheduleResultExporter : IScheduleResultExporter
{
    private readonly ScheduleResultExportOptions _options;
    private readonly ILogger<ExcelScheduleResultExporter> _logger;
    private readonly IFileSystem _fileSystem;

    public ExcelScheduleResultExporter(
        IOptions<ScheduleResultExportOptions> options,
        ILogger<ExcelScheduleResultExporter>? logger = null,
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
        _logger = logger ?? NullLogger<ExcelScheduleResultExporter>.Instance;
        _fileSystem = fileSystem ?? new FileSystem();
    }

    public Task<string> ExportAsync()
    {
        var writer = new ExcelSchedulerConfigWriter(_fileSystem);
        var fullPath = writer.WriteScheduleResult(_options.ScheduleResult, _options.FilePath);
        _logger.LogInformation("Excel template written to {FilePath}", fullPath);
        return Task.FromResult(fullPath);
    }
}