using System.Collections.ObjectModel;
using System.IO;
using CommunityToolkit.Mvvm.ComponentModel;
using CommunityToolkit.Mvvm.Input;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Options;
using SchedulePlanner.Cli;
using SchedulePlanner.Core;
using SchedulePlanner.ImportExport;
using SchedulePlanner.Wpf.Services;

namespace SchedulePlanner.Wpf.ViewModels;

public partial class MainViewModel : ObservableObject
{
    private readonly IDialogService _dialogService;
    private readonly IServiceScopeFactory _serviceScopeFactory;

    [ObservableProperty] private string _statusMessage = "Ready.";
    [ObservableProperty] private bool _isBusy;
    [ObservableProperty] private double _jobProgress;
    [ObservableProperty] private string _temporalStatus = "Idle";

    // 1. Replaced "Settings" with strongly-typed SchedulerOptions
    [ObservableProperty] private SchedulerOptions _options = new();

    // 2. Replaced "Results" with the core ScheduleResult
    [ObservableProperty] private ScheduleResult? _scheduleResult;

    // Observable wrappers for editing collections (keeps Core project clean)
    public ObservableCollection<Teacher> Teachers { get; } = new();
    public ObservableCollection<Class> Classes { get; } = new();

    // UI Helper for the Weekly Grid View
    [ObservableProperty]
    [NotifyPropertyChangedFor(nameof(CurrentWeeklyBlocks))]
    private TeacherScheduleResult? _selectedTeacherSchedule;

    public IEnumerable<ScheduleBlockResult>? CurrentWeeklyBlocks =>
        SelectedTeacherSchedule?.ToWeekSchedule().Blocks;

    public MainViewModel(IDialogService dialogService, IServiceScopeFactory serviceScopeFactory)
    {
        _dialogService = dialogService;
        _serviceScopeFactory = serviceScopeFactory;

        // Initialize with default data or empty state
        LoadDefaultData();
    }

    private void LoadDefaultData()
    {
        using var scope = _serviceScopeFactory.CreateScope();
        var options = scope.ServiceProvider.GetRequiredService<IOptions<SchedulerOptions>>().Value;
        foreach (var teacher in options.Teachers)
        {
            Teachers.Add(teacher);
        }
        foreach (var @class in options.Classes)
        {
            Classes.Add(@class);
        }
    }

    [RelayCommand]
    internal async Task ExportSettingsAsync() => await HandleExport("Settings_Export.xlsx", SettingsExport);

    [RelayCommand]
    internal async Task ExportResultsAsync() => await HandleExport("Schedule_Results.xlsx", ScheduleExport);

    private async Task<string> SettingsExport(ExportService exporter, string path)
    {
        return await exporter.ExportTemplateAsync(Options, path, addTimestamp: false);
    }

    private async Task<string> ScheduleExport(ExportService exporter, string path)
    {
        if (ScheduleResult == null)
        {
            throw new InvalidOperationException("No schedule results available to export.");
        }
        var exportOptions = new ScheduleResultExportOptions
        {
            ScheduleResult = ScheduleResult,
            FilePath = path
        };
        return await exporter.ExportToExcelAsync(exportOptions);
    }

    private async Task HandleExport(string defaultName, Func<ExportService, string, Task<string>> taskFactory)
    {
        var path = _dialogService.SaveFile(defaultName);
        if (string.IsNullOrWhiteSpace(path)) return;

        try
        {
            IsBusy = true;
            StatusMessage = $"Exporting to {Path.GetFileName(path)}...";
            using var scope = _serviceScopeFactory.CreateScope();
            var exporter = scope.ServiceProvider.GetRequiredService<ExportService>();
            var resultPath = await taskFactory(exporter, path);
            _dialogService.ShowMessage("Success", $"File exported successfully:\n\n{resultPath}");
        }
        catch (Exception ex)
        {
            _dialogService.ShowError("Export Failed", ex.Message);
        }
        finally
        {
            IsBusy = false;
            StatusMessage = "Ready.";
        }
    }

    [RelayCommand]
    internal async Task RunSolveAsync()
    {
        if (IsBusy) return;

        try
        {
            IsBusy = true;
            StatusMessage = "Loading configuration...";
            TemporalStatus = "Initializing Solver...";

            // Sync observable UI collections back to the Options model
            Options.Teachers = Teachers.ToList();
            Options.Classes = Classes.ToList();

            using var scope = _serviceScopeFactory.CreateScope();
            var solver = scope.ServiceProvider.GetRequiredService<SchedulingService>();

            var progress = new Progress<SolverProgress>(p => {
                JobProgress = p.CurrentGap.GetValueOrDefault();
                TemporalStatus = p.Message;
            });

            ScheduleResult = await Task.Run(() => solver.RunAsync(default, progress));

            if (ScheduleResult.HasSolution)
            {
                SelectedTeacherSchedule = ScheduleResult.TeacherSchedules.FirstOrDefault();
                StatusMessage = $"Success: Optimal schedule found.";
            }
            else
            {
                StatusMessage = $"No solution: {ScheduleResult.Status}";
            }
        }
        catch (Exception ex)
        {
            _dialogService.ShowError("Solver Error", ex.Message);
        }
        finally
        {
            IsBusy = false;
            TemporalStatus = "Idle";
        }
    }

    [RelayCommand]
    internal async Task RunDemoAsync()
    {
        if (IsBusy) return;

        try
        {
            IsBusy = true;
            StatusMessage = "Running demo scheduler (Large K12 School)...";
            TemporalStatus = "Initializing Solver...";

            // Sync observable UI collections back to the Options model
            Options.Teachers = Teachers.ToList();
            Options.Classes = Classes.ToList();

            using var scope = _serviceScopeFactory.CreateScope();
            var solver = scope.ServiceProvider.GetRequiredService<DemoScheduleRunner>();

            // Progress reporting logic remains bound to JobProgress
            var progress = new Progress<SolverProgress>(p => {
                JobProgress = p.CurrentGap.GetValueOrDefault();
                TemporalStatus = p.Message;
            });

            ScheduleResult = await Task.Run(() => solver.RunAsync(default, progress));

            if (ScheduleResult.HasSolution)
            {
                SelectedTeacherSchedule = ScheduleResult.TeacherSchedules.FirstOrDefault();
                StatusMessage = $"Success: Optimal schedule found.";
            }
            else
            {
                StatusMessage = $"No solution: {ScheduleResult.Status}";
            }
        }
        catch (Exception ex)
        {
            _dialogService.ShowError("Solver Error", ex.Message);
        }
        finally
        {
            IsBusy = false;
            TemporalStatus = "Idle";
        }
    }
}