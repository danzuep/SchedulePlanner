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
    }
}