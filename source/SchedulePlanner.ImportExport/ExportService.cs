using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using Microsoft.Extensions.Options;
using SchedulePlanner.Core;
using SchedulePlanner.ImportExport.Calendar;
using SchedulePlanner.ImportExport.Csv;
using SchedulePlanner.ImportExport.Excel;

namespace SchedulePlanner.ImportExport
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

        public async Task RunAsync(CancellationToken cancellationToken = default, IProgress<SolverProgress>? progress = null, TimeSpan? progressTimeout = null)
        {
            var importExportConfig = ImportExportOptions.Default;
            _ = await ExportTemplateAsync(_config, importExportConfig.FilePath).ConfigureAwait(false);
        }

        public Task<string> ExportTemplateAsync(SchedulerOptions config, string filePath, bool addTimestamp = false)
        {
            var writer = new ExcelSchedulerConfigWriter();
            var fullPath = writer.WriteSchedulerOptions(config, filePath, addTimestamp);
            _logger.LogInformation("Excel template written to {FilePath}", fullPath);
            return Task.FromResult(fullPath);
        }

        public async Task<string> ExportToExcelAsync(ScheduleResult result, string filePath)
        {
            var options = new ScheduleResultExportOptions
            {
                ScheduleResult = result,
                FilePath = filePath
            };
            return await ExportToExcelAsync(options).ConfigureAwait(false);
        }

        public async Task<string> ExportToExcelAsync(ScheduleResultExportOptions options)
        {
            var exporter = new ExcelScheduleResultExporter(options);
            var fullPath = await exporter.ExportAsync();
            return fullPath;
        }

        public async Task<string> ExportToICalAsync(ScheduleResultExportOptions options)
        {
            var exporter = new CalendarScheduleResultExporter(options);
            var fullPath = await exporter.ExportAsync();
            return fullPath;
        }

        public async Task<string> ExportToCsvAsync(ScheduleResultExportOptions options)
        {
            var exporter = new CsvScheduleResultExporter(options);
            var fullPath = await exporter.ExportAsync();
            return fullPath;
        }
    }
}