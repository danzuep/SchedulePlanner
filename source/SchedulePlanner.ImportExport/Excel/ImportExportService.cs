using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using Microsoft.Extensions.Options;
using SchedulePlanner.Core;

namespace SchedulePlanner.ImportExport.Excel
{
    public sealed class ImportExportService : IService
    {
        private readonly IServiceScopeFactory _serviceScopeFactory;
        private readonly ILogger<ImportExportService> _logger;

        public ImportExportService(IServiceScopeFactory serviceScopeFactory, ILogger<ImportExportService>? logger = null)
        {
            _serviceScopeFactory = serviceScopeFactory ?? throw new ArgumentNullException(nameof(serviceScopeFactory));
            _logger = logger ?? NullLogger<ImportExportService>.Instance;
        }

        public async Task RunAsync(CancellationToken cancellationToken = default, IProgress<SolverProgress>? progress = null, TimeSpan? progressTimeout = null)
        {
            using var scope = _serviceScopeFactory.CreateScope();
            var provider = scope.ServiceProvider;
            var importExportOptions = provider.GetRequiredService<IOptionsSnapshot<ImportExportOptions>>().Value;

            _logger.LogDebug("Exporting template...");
            var exportService = provider.GetRequiredService<ExportService>();
            var schedulerOptions = provider.GetRequiredService<IOptionsSnapshot<SchedulerOptions>>().Value;
            var configFile = await exportService.ExportTemplateAsync(schedulerOptions, importExportOptions.FilePath);
            _logger.LogDebug("Export completed successfully.");

            _logger.LogDebug("Processing workbook...");
            var schedulerLogger = provider.GetRequiredService<ILogger<ExcelSchedulerConfigReader>>();
            var schedulingLogger = provider.GetRequiredService<ILogger<SchedulingService>>();
            var importOptions = new ImportExportOptions { FilePath = configFile };
            var reader = new ExcelSchedulerConfigReader(importOptions, schedulerLogger);
            var importService = new ImportService(reader, schedulingLogger);
            var result = await importService.RunAsync(cancellationToken, progress).ConfigureAwait(false);
            _logger.LogDebug("Processing completed successfully.");
            var filePath = await exportService.ExportToExcelAsync(result, importExportOptions.FilePath);
            _logger.LogDebug("Result written successfully.");
        }
    }
}