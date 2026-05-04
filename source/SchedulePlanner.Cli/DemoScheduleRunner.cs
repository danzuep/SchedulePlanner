namespace SchedulePlanner.Cli;

using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using SchedulePlanner.Core;
using SchedulePlanner.ImportExport;
using SchedulePlanner.ImportExport.Excel;

public class DemoScheduleRunner : IService<ScheduleResult>
{
    private readonly ILogger<DemoScheduleRunner> _logger;
    private readonly SchedulerOptions _options;
    private readonly bool _useSmallDemo;
    private readonly bool _useUnsolvableDemo;
    private readonly TimeSpan? _progressTimeout;
    private readonly string? _exportFileName;
    private readonly bool _disableExports;

    public DemoScheduleRunner(ILogger<DemoScheduleRunner>? logger = null, bool useSmallDemo = false, bool useUnsolvableDemo = false, TimeSpan? progressTimeout = null, string? exportFileName = null, bool disableExports = false)
    {
        _options = useSmallDemo ? DemoDataFactory.CreateSmallK12SchoolDemo() :
                   useUnsolvableDemo ? DemoDataFactory.CreateUnsolvableDemo() : DemoDataFactory.CreateLargeK12SchoolDemo();
        _logger = logger ?? NullLogger<DemoScheduleRunner>.Instance;
        _useSmallDemo = useSmallDemo;
        _useUnsolvableDemo = useUnsolvableDemo;
        _progressTimeout = progressTimeout;
        _exportFileName = exportFileName;
        _disableExports = disableExports;
    }

    public async Task<ScheduleResult> RunAsync(CancellationToken cancellationToken = default, IProgress<SolverProgress>? progress = null, TimeSpan? progressTimeout = null)
    {
        var demoType = _useUnsolvableDemo ? "Unsolvable" : _useSmallDemo ? "Small" : "Large";
        _logger.LogInformation("Running demo schedule ({DemoType} K12 School)...", demoType);

        // Build a minimal service scope for running the demo
        using var host = Host.CreateDefaultBuilder()
            .ConfigureServices((context, services) =>
                services.AddDemoScheduleServices())
            .Build();

        using var scope = host.Services.CreateScope();
        var configValidator = scope.ServiceProvider.GetRequiredService<IConfigValidator>();
        var classAssignmentBuilder = scope.ServiceProvider.GetRequiredService<IClassAssignmentBuilder>();
        var constraintBuilder = scope.ServiceProvider.GetRequiredService<IConstraintBuilder>();
        var optimizationBuilder = scope.ServiceProvider.GetRequiredService<IOptimizationBuilder>();
        var resultBuilder = scope.ServiceProvider.GetRequiredService<IResultBuilder>();
        var scheduleLogger = scope.ServiceProvider.GetRequiredService<IScheduleLogger>();

        var service = new SchedulingService(
            _options,
            NullLogger<SchedulingService>.Instance,
            configValidator,
            classAssignmentBuilder,
            constraintBuilder,
            optimizationBuilder,
            resultBuilder,
            scheduleLogger);

        var result = await service.RunAsync(cancellationToken, progress, _progressTimeout);

        _logger.LogInformation("Solution found: {HasSolution}", result.HasSolution);
        if (result.HasSolution)
        {
            _logger.LogInformation("Teachers scheduled: {TeacherCount}", result.TeacherSchedules.Count);
            _logger.LogInformation("Classes scheduled: {ClassCount}", result.Classes.Count);
            if (result.StreamSchedules?.Count > 0)
                _logger.LogInformation("Stream schedules: {StreamCount}", result.StreamSchedules.Count);

            if (!_disableExports)
            {
                var exportService = scope.ServiceProvider.GetRequiredService<ExportService>();
                var importExportConfig = ImportExportOptions.Default;

                // Use custom file name if provided to avoid conflicts between concurrent tests
                if (_exportFileName != null)
                {
                    importExportConfig.FileName = _exportFileName;
                }

                var exportOptions = new ScheduleResultExportOptions
                {
                    ScheduleResult = result,
                    FilePath = importExportConfig.FilePath
                };

                var xlsxPath = await exportService.ExportToExcelAsync(exportOptions);
                _logger.LogInformation("Excel summary written to: {FilePath}", xlsxPath);

                var icalPath = await exportService.ExportToICalAsync(exportOptions);
                _logger.LogInformation("iCal schedule written to: {FilePath}", icalPath);

                var csvPath = await exportService.ExportToCsvAsync(exportOptions);
                _logger.LogInformation("CSV summary written to: {FilePath}", csvPath);
            }
        }
        else
        {
            _logger.LogWarning("No solution found. Status: {Status}", result.Status);
        }

        _logger.LogInformation("Demo schedule run completed in {Duration}", result.RunDuration);

        return result;
    }
}