using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using SchedulePlanner.Core;
using SchedulePlanner.ImportExport.Excel;

public static partial class Program
{
    public sealed class ExportService : IService
    {
        private readonly ILogger<ExportService> _logger;

        public ExportService(ILogger<ExportService>? logger = null)
        {
            _logger = logger ?? NullLogger<ExportService>.Instance;
        }

        public Task RunAsync(CancellationToken cancellationToken = default)
        {
            var importExportConfig = new ImportExportConfig
            {
#if DEBUG
                ImportDirectory = "../..",
#endif
                ImportFileName = "schedule-config.xlsx"
            };
            var fullPath = ExcelTemplateWriter.WriteTemplate(importExportConfig);
            _logger.LogInformation("Excel template written to {FilePath}", fullPath);
            return Task.CompletedTask;
        }
    }
}