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
            await ExportAsync(_config, importExportConfig.FilePath).ConfigureAwait(false);
        }

        public Task ExportAsync(SchedulerOptions config, string filePath)
        {
            var fullPath = ExcelSchedulerConfigWriter.WriteWorkbook(config, filePath);
            _logger.LogInformation("Excel template written to {FilePath}", fullPath);
            return Task.CompletedTask;
        }
    }
}