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

    public DemoScheduleRunner(ILogger<DemoScheduleRunner>? logger = null, bool useSmallDemo = false)
    {
        _options = useSmallDemo ? DemoDataFactory.CreateSmallK12SchoolDemo() : DemoDataFactory.CreateLargeK12SchoolDemo();
        _logger = logger ?? NullLogger<DemoScheduleRunner>.Instance;
    }

    public async Task<ScheduleResult> RunAsync(CancellationToken cancellationToken = default, IProgress<SolverProgress>? progress = null)
    {
        _logger.LogInformation("Running demo schedule (Large K12 School)...");

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

        var result = await service.RunAsync();

        _logger.LogInformation("Solution found: {HasSolution}", result.HasSolution);
        if (result.HasSolution)
        {
            _logger.LogInformation("Teachers scheduled: {TeacherCount}", result.TeacherSchedules.Count);
            _logger.LogInformation("Classes scheduled: {ClassCount}", result.Classes.Count);
            if (result.StreamSchedules?.Count > 0)
                _logger.LogInformation("Stream schedules: {StreamCount}", result.StreamSchedules.Count);

            var exportService = scope.ServiceProvider.GetRequiredService<ExportService>();
            var importExportConfig = ImportExportOptions.Default;

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
        else
        {
            _logger.LogWarning("No solution found. Status: {Status}", result.Status);
        }

        _logger.LogInformation("Demo schedule run completed in {Duration}", result.RunDuration);

        return result;
    }
}