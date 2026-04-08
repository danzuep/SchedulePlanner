using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using Microsoft.Extensions.Options;
using SchedulePlanner.Core;

namespace SchedulePlanner.ImportExport.Excel
{
    public sealed class ImportExportService : IService
    {
        private readonly ImportExportOptions _options;
        private readonly IServiceScopeFactory _serviceScopeFactory;
        private readonly ILogger<ImportExportService> _logger;

        public ImportExportService(IServiceScopeFactory serviceScopeFactory, ILogger<ImportExportService>? logger = null)
        {
            _serviceScopeFactory = serviceScopeFactory ?? throw new ArgumentNullException(nameof(serviceScopeFactory));
            _logger = logger ?? NullLogger<ImportExportService>.Instance;
            using var scope = _serviceScopeFactory.CreateScope();
            var config = scope.ServiceProvider.GetRequiredService<IOptions<ImportExportOptions>>();
            _options = config.Value;
        }

        public async Task RunAsync(CancellationToken cancellationToken = default)
        {
            using var scope = _serviceScopeFactory.CreateScope();

            _logger.LogDebug("Exporting template...");
            var exportService = scope.ServiceProvider.GetRequiredService<ExportService>();
            var config = scope.ServiceProvider.GetRequiredService<IOptionsSnapshot<SchedulerOptions>>();
            await exportService.ExportAsync(config.Value, _options.FilePath);
            _logger.LogDebug("Export completed successfully.");

            _logger.LogDebug("Processing workbook...");
            var schedulerLogger = scope.ServiceProvider.GetRequiredService<ILogger<ExcelSchedulerConfigReader>>();
            var schedulingLogger = scope.ServiceProvider.GetRequiredService<ILogger<SchedulingService>>();
            var reader = new ExcelSchedulerConfigReader(_options, schedulerLogger);
            var importService = new ImportService(reader, schedulingLogger);
            var result = await importService.RunAsync();
            _logger.LogDebug("Processing completed successfully.");
            var filePath = await exportService.ExportAsync(result, _options.FilePath, addTimestamp: true);
            _logger.LogDebug("Result written successfully.");
        }
    }
}