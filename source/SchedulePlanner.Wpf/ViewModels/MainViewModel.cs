using System.IO;
using System.Windows;
using CommunityToolkit.Mvvm.ComponentModel;
using CommunityToolkit.Mvvm.Input;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using SchedulePlanner.Core;
using SchedulePlanner.ImportExport.Excel;
using SchedulePlanner.Wpf.Helpers;
using SchedulePlanner.Wpf.Services;
using SchedulePlanner.Wpf.Views;

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

    [ObservableProperty]
    private string statusMessage = "Ready.";

    [ObservableProperty]
    private string? inputWorkbookPath;

    [ObservableProperty]
    private string? outputWorkbookPath;

    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(IsButtonEnabled))]
    private bool isBusy;

    [ObservableProperty]
    private SchedulerOptions? demoOptions;
    partial void OnDemoOptionsChanged(SchedulerOptions? value)
    {
        DemoInfoText = value == null 
            ? "No demo data generated"
            : $"{value.Teachers?.Count ?? 0} teachers, {value.Classes?.Count ?? 0} classes, {value.Rooms?.Count ?? 0} rooms";
        RunDemoScheduleCommand.NotifyCanExecuteChanged();
    }

    [ObservableProperty]
    private string demoInfoText = "No demo data generated";

    public bool IsButtonEnabled => !IsBusy;

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

    [RelayCommand]
    private void GenerateLargeK12Demo()
    {
        StatusMessage = "Generating large K12 school demo data...";
        try
        {
            DemoOptions = DemoDataFactory.CreateLargeK12SchoolDemo();
            StatusMessage = $"Generated demo: {DemoOptions.Teachers.Count} teachers, {DemoOptions.Classes.Count} classes, {DemoOptions.Rooms.Count} rooms.";
        }
        catch (Exception ex)
        {
            StatusMessage = "Demo generation failed.";
            _dialogService.ShowError("Error", ex.Message);
        }
    }

    [RelayCommand]
    private async Task RunDemoSchedule()
    {
        if (DemoOptions == null)
        {
            // Auto-generate demo data if not already present
            GenerateLargeK12Demo();
            return;
        }
        await RunScheduleForOptions(DemoOptions, "Demo");
    }

    [RelayCommand(AllowConcurrentExecutions = false)]
    private async Task ExportWorkbookAsync()
    {
        if (string.IsNullOrWhiteSpace(OutputWorkbookPath))
            return;
        try
        {
            IsBusy = true;
            StatusMessage = "Exporting template...";

            using var scope = _serviceScopeFactory.CreateScope();
            var service = scope.ServiceProvider.GetRequiredService<ExportService>();
            var config = scope.ServiceProvider.GetRequiredService<IOptionsSnapshot<SchedulerOptions>>();
            await service.ExportAsync(config.Value, OutputWorkbookPath);

            StatusMessage = "Export completed successfully.";

            _dialogService.ShowMessage("Success", "Export completed successfully.");
        }
        catch (Exception ex)
        {
            StatusMessage = "Export failed.";
            _dialogService.ShowError("Error", ex.Message);
        }
        finally
        {
            IsBusy = false;
        }
    }

    [RelayCommand(AllowConcurrentExecutions = false)]
    private async Task ProcessWorkbookAsync()
    {
        if (string.IsNullOrWhiteSpace(InputWorkbookPath))
            InputWorkbookPath = Path.GetFullPath(ImportExportOptions.Default.FilePath);
        try
        {
            IsBusy = true;
            StatusMessage = "Processing workbook...";

            var options = new ImportExportOptions
            {
                FilePath = InputWorkbookPath ?? string.Empty
            };

            using var scope = _serviceScopeFactory.CreateScope();
            var logger = scope.ServiceProvider.GetRequiredService<ILogger<ExcelSchedulerConfigReader>>();
            var inner = scope.ServiceProvider.GetRequiredService<ILogger<SchedulingService>>();
            await using var schedulingLogger = new FileLogger<SchedulingService>(options, inner);
            var reader = new ExcelSchedulerConfigReader(options, logger);
            var importService = new ImportService(reader, schedulingLogger);
            var result = await importService.RunAsync();

            StatusMessage = "Processing completed successfully.";

            var service = scope.ServiceProvider.GetRequiredService<ExportService>();
            var filePath = await service.ExportAsync(result, options.FilePath, addTimestamp: true);

            StatusMessage = "Result written successfully.";

            _dialogService.ShowMessage("Success", "Schedule planned successfully." +
                Environment.NewLine + Environment.NewLine +
                "Template written to " + filePath);
        }
        catch (Exception ex)
        {
            StatusMessage = "Processing failed.";
            _dialogService.ShowError("Error", ex.Message);
        }
        finally
        {
            IsBusy = false;
        }
    }

    private async Task RunScheduleForOptions(SchedulerOptions options, string sourceLabel)
    {
        try
        {
            IsBusy = true;
            StatusMessage = $"Running {sourceLabel} schedule...";

            using var scope = _serviceScopeFactory.CreateScope();
            var logger = scope.ServiceProvider.GetRequiredService<ILogger<SchedulingService>>();
            var configValidator = scope.ServiceProvider.GetRequiredService<IConfigValidator>();
            var classAssignmentBuilder = scope.ServiceProvider.GetRequiredService<IClassAssignmentBuilder>();
            var constraintBuilder = scope.ServiceProvider.GetRequiredService<IConstraintBuilder>();
            var optimizationBuilder = scope.ServiceProvider.GetRequiredService<IOptimizationBuilder>();
            var resultBuilder = scope.ServiceProvider.GetRequiredService<IResultBuilder>();

            var service = new SchedulingService(
                Options.Create(options),
                logger,
                configValidator,
                classAssignmentBuilder,
                constraintBuilder,
                optimizationBuilder,
                resultBuilder,
                null);

            var result = await service.RunAsync();

            StatusMessage = "Processing completed successfully.";

            var exportService = scope.ServiceProvider.GetRequiredService<ExportService>();
            var defaultPath = Path.GetFullPath(ImportExportOptions.Default.FilePath);
            var filePath = await exportService.ExportAsync(result, defaultPath, addTimestamp: true);

            StatusMessage = "Result written successfully.";
            _dialogService.ShowMessage("Success", "Schedule planned successfully."
                + Environment.NewLine + Environment.NewLine
                + "Template written to " + filePath);

            // Update the schedule timeline display
            UpdateScheduleSummary(result);
        }
        catch (Exception ex)
        {
            StatusMessage = "Schedule failed.";
            _dialogService.ShowError("Error", ex.Message);
        }
        finally
        {
            IsBusy = false;
        }
    }

    private void UpdateScheduleSummary(ScheduleResult result)
    {
        var summary = result.HasSolution
            ? $"Solution found! {result.TeacherSchedules.Count} teachers, {result.Classes.Count} classes scheduled."
            : $"No solution: {result.Status}";

        var mainView = Application.Current?.Windows.OfType<MainWindow>().FirstOrDefault() as MainWindow;
        if (mainView != null)
        {
            var mainControl = mainView.Content as MainView;
            if (mainControl != null)
            {
                mainControl.Dispatcher.Invoke(() =>
                {
                    mainControl.ScheduleSummaryText.Text = summary;
                });
            }
        }
    }
}
