using System.IO;
using CommunityToolkit.Mvvm.ComponentModel;
using CommunityToolkit.Mvvm.Input;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using SchedulePlanner.Cli;
using SchedulePlanner.Core;
using SchedulePlanner.ImportExport;
using SchedulePlanner.ImportExport.Excel;
using SchedulePlanner.Wpf.Helpers;
using SchedulePlanner.Wpf.Services;

namespace SchedulePlanner.Wpf.ViewModels;

public partial class MainViewModel : ObservableObject
{
    private readonly IDialogService _dialogService;
    private readonly IServiceScopeFactory _serviceScopeFactory;

    public MainViewModel(
        IDialogService dialogService,
        IServiceScopeFactory serviceScopeFactory)
    {
        _dialogService = dialogService;
        _serviceScopeFactory = serviceScopeFactory;
    }

    #region Observable Properties

    [ObservableProperty]
    private string _statusMessage = "Ready.";

    [ObservableProperty]
    private string? _inputWorkbookPath;

    [ObservableProperty]
    private string? _outputWorkbookPath;

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(IsButtonEnabled))]
    [NotifyCanExecuteChangedFor(nameof(ExportWorkbookCommand))]
    [NotifyCanExecuteChangedFor(nameof(ProcessWorkbookCommand))]
    [NotifyCanExecuteChangedFor(nameof(RunDemoScheduleCommand))]
    private bool _isBusy;

    [ObservableProperty]
    private double _jobProgress;

    [ObservableProperty]
    private string _temporalStatus = "Idle";

    [ObservableProperty]
    private string _scheduleSummaryText = "Generate or process a schedule to see timeline visualization.";

    [ObservableProperty]
    private SchedulerOptions? _demoOptions;

    [ObservableProperty]
    private string _demoInfoText = "No demo data generated";

    public bool IsButtonEnabled => !IsBusy;

    #endregion

    #region Partial Methods

    partial void OnDemoOptionsChanged(SchedulerOptions? value)
    {
        DemoInfoText = value == null
            ? "No demo data generated"
            : $"{value.Teachers?.Count ?? 0} teachers, {value.Classes?.Count ?? 0} classes, {value.Rooms?.Count ?? 0} rooms";
    }

    #endregion

    #region Commands

    [RelayCommand]
    private void BrowseInputWorkbook()
    {
        StatusMessage = "Browse for an input Excel workbook.";
        var selected = _dialogService.OpenFile();
        if (!string.IsNullOrWhiteSpace(selected))
            InputWorkbookPath = selected;
    }

    [RelayCommand]
    private void BrowseOutputWorkbook()
    {
        StatusMessage = "Browse for where to output an Excel template.";
        var defaultPath = Path.GetFullPath(ImportExportOptions.Default.FilePath);
        var selected = _dialogService.SaveFile(defaultPath);
        if (!string.IsNullOrWhiteSpace(selected))
            OutputWorkbookPath = selected;
    }

    [RelayCommand(CanExecute = nameof(IsButtonEnabled))]
    private void GenerateLargeK12Demo()
    {
        StatusMessage = "Generating large K12 school demo data...";
        try
        {
            DemoOptions = DemoDataFactory.CreateLargeK12SchoolDemo();
            StatusMessage = $"Generated demo: {DemoOptions.Teachers.Count} teachers, {DemoOptions.Classes.Count} classes.";
        }
        catch (Exception ex)
        {
            StatusMessage = "Demo generation failed.";
            _dialogService.ShowError("Error", ex.Message);
        }
    }

    [RelayCommand(CanExecute = nameof(IsButtonEnabled))]
    private async Task RunDemoSchedule()
    {
        if (DemoOptions == null)
        {
            GenerateLargeK12Demo();
            return;
        }

        try
        {
            IsBusy = true;
            TemporalStatus = "Running Temporal Activity...";
            StatusMessage = "Solving K-12 Schedule...";

            using var scope = _serviceScopeFactory.CreateScope();
            var runner = scope.ServiceProvider.GetRequiredService<DemoScheduleRunner>();

            // Note: If DemoScheduleRunner supports IProgress, you would bind it to JobProgress here
            await runner.RunAsync();

            StatusMessage = "Demo Solve Complete.";
        }
        catch (Exception ex)
        {
            _dialogService.ShowError("Solve Failed", ex.Message);
        }
        finally
        {
            IsBusy = false;
            TemporalStatus = "Completed";
        }
    }

    [RelayCommand(AllowConcurrentExecutions = false, CanExecute = nameof(IsButtonEnabled))]
    private async Task ExportWorkbookAsync()
    {
        if (string.IsNullOrWhiteSpace(OutputWorkbookPath)) return;

        try
        {
            IsBusy = true;
            StatusMessage = "Exporting template...";

            using var scope = _serviceScopeFactory.CreateScope();
            var service = scope.ServiceProvider.GetRequiredService<ExportService>();
            var config = scope.ServiceProvider.GetRequiredService<IOptionsSnapshot<SchedulerOptions>>();
            await service.ExportTemplateAsync(config.Value, OutputWorkbookPath);

            StatusMessage = "Export completed successfully.";
            _dialogService.ShowMessage("Success", "Export completed successfully.");
        }
        catch (Exception ex)
        {
            StatusMessage = "Export failed.";
            _dialogService.ShowError("Error", ex.Message);
        }
        finally { IsBusy = false; }
    }

    [RelayCommand(AllowConcurrentExecutions = false, CanExecute = nameof(IsButtonEnabled))]
    private async Task ProcessWorkbookAsync()
    {
        if (string.IsNullOrWhiteSpace(InputWorkbookPath))
            InputWorkbookPath = Path.GetFullPath(ImportExportOptions.Default.FilePath);

        try
        {
            IsBusy = true;
            TemporalStatus = "Processing Workflow";
            StatusMessage = "Processing workbook via Temporal...";

            var options = new ImportExportOptions { FilePath = InputWorkbookPath ?? string.Empty };

            using var scope = _serviceScopeFactory.CreateScope();
            var logger = scope.ServiceProvider.GetRequiredService<ILogger<ExcelSchedulerConfigReader>>();
            var inner = scope.ServiceProvider.GetRequiredService<ILogger<SchedulingService>>();

            await using var schedulingLogger = new FileLogger<SchedulingService>(options, inner);
            var reader = new ExcelSchedulerConfigReader(options, logger);
            var importService = new ImportService(reader, schedulingLogger);

            var result = await importService.RunAsync();

            var service = scope.ServiceProvider.GetRequiredService<ExportService>();
            var filePath = await service.ExportToExcelAsync(result, options.FilePath);

            StatusMessage = "Result written successfully.";
            UpdateScheduleSummary(result);

            _dialogService.ShowMessage("Success", $"Schedule planned successfully.\n\nTemplate written to {filePath}");
        }
        catch (Exception ex)
        {
            StatusMessage = "Processing failed.";
            _dialogService.ShowError("Error", ex.Message);
        }
        finally { IsBusy = false; TemporalStatus = "Idle"; }
    }

    #endregion

    private void UpdateScheduleSummary(ScheduleResult result)
    {
        ScheduleSummaryText = result.HasSolution
            ? $"Solution found! {result.TeacherSchedules.Count} teachers, {result.Classes.Count} classes scheduled."
            : $"No solution: {result.Status}";
    }
}