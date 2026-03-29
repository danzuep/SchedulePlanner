using System.IO;
using CommunityToolkit.Mvvm.ComponentModel;
using CommunityToolkit.Mvvm.Input;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using SchedulePlanner.Core;
using SchedulePlanner.ImportExport.Excel;
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

    [ObservableProperty]
    private string statusMessage = "Ready.";

    [ObservableProperty]
    private string? inputWorkbookPath;

    [ObservableProperty]
    private string? outputWorkbookPath;

    [ObservableProperty]
    private bool isBusy;

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
            //var schedulingLogger = scope.ServiceProvider.GetRequiredService<ILogger<SchedulingService>>();
            var schedulingLogger = new FileLogger(options);
            var reader = new ExcelSchedulerConfigReader(options, logger);
            var importService = new ImportService(reader, schedulingLogger);
            await importService.RunAsync();

            StatusMessage = "Processing completed successfully.";

            var log = schedulingLogger.ReadLog();

            _dialogService.ShowMessage("Success", "Schedule planned successfully." +
                Environment.NewLine + Environment.NewLine + log);
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
}