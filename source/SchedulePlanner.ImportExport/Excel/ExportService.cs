using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using Microsoft.Extensions.Options;
using SchedulePlanner.Core;

namespace SchedulePlanner.ImportExport.Excel
{
    public sealed class ExportService : IService
    {
        private readonly SchedulerConfig _config;
        private readonly ILogger<ExportService> _logger;

        public ExportService(IOptions<SchedulerConfig> config, ILogger<ExportService>? logger = null)
        {
            _config = config.Value;
            _logger = logger ?? NullLogger<ExportService>.Instance;
        }

        public Task RunAsync(CancellationToken cancellationToken = default)
        {
            var importExportConfig = ImportExportConfig.Default;
            var fullPath = ExcelSchedulerConfigWriter.WriteWorkbook(_config, importExportConfig.FilePath);
            _logger.LogInformation("Excel template written to {FilePath}", fullPath);
            return Task.CompletedTask;
        }
    }
}