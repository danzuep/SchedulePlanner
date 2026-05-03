namespace SchedulePlanner.Cli;

using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using SchedulePlanner.Core;
using SchedulePlanner.ImportExport;
using SchedulePlanner.ImportExport.Excel;

public class DemoScheduleRunner
{
    private readonly ILogger<DemoScheduleRunner> _logger;

    public DemoScheduleRunner(ILogger<DemoScheduleRunner> logger)
    {
        _logger = logger;
    }

    public async Task<ScheduleResult> RunAsync(SchedulerOptions options = null!)
    {
        options ??= DemoDataFactory.CreateLargeK12SchoolDemo();

        _logger.LogInformation("Running demo schedule (Large K12 School)...");

        // Build a minimal service scope for running the demo
        using var host = Host.CreateDefaultBuilder()
            .ConfigureServices((context, services) =>
            {
                services.AddSingleton<ImportExportService>();
                services.AddSingleton<ExportService>();
                services.AddSingleton<ImportService>();
                services.AddSingleton<IConfigValidator, ConfigValidator>();
                services.AddSingleton<IClassAssignmentBuilder, ClassAssignmentBuilder>();
                services.AddSingleton<IConstraintBuilder, ConstraintBuilder>();
                services.AddSingleton<IOptimizationBuilder, OptimizationBuilder>();
                services.AddSingleton<IResultBuilder, ResultBuilder>();
                services.AddSingleton<IScheduleLogger, ScheduleLogger>();
            })
            .Build();

        using var scope = host.Services.CreateScope();
        var configValidator = scope.ServiceProvider.GetRequiredService<IConfigValidator>();
        var classAssignmentBuilder = scope.ServiceProvider.GetRequiredService<IClassAssignmentBuilder>();
        var constraintBuilder = scope.ServiceProvider.GetRequiredService<IConstraintBuilder>();
        var optimizationBuilder = scope.ServiceProvider.GetRequiredService<IOptimizationBuilder>();
        var resultBuilder = scope.ServiceProvider.GetRequiredService<IResultBuilder>();
        var scheduleLogger = scope.ServiceProvider.GetRequiredService<IScheduleLogger>();

        var service = new SchedulingService(
            Microsoft.Extensions.Options.Options.Create(options),
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

            var filePath = await exportService.ExportAsync(result, importExportConfig.FilePath, addTimestamp: true);
            _logger.LogInformation("Results exported to: {FilePath}", filePath);

            var icalPath = await exportService.ExportToICalAsync(result, importExportConfig.FilePath, addTimestamp: true);
            _logger.LogInformation("iCal exported to: {ICalPath}", icalPath);

            var csvPath = await exportService.ExportToCsvAsync(result, importExportConfig.FilePath, addTimestamp: true);
            _logger.LogInformation("CSV exported to: {CsvPath}", csvPath);
        }
        else
        {
            _logger.LogWarning("No solution found. Status: {Status}. RunDuration: {Duration}ms", result.Status, result.RunDuration?.TotalMilliseconds);
        }

        return result;
    }
}