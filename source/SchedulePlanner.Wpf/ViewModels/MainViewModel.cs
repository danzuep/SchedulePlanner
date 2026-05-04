using System.Collections.ObjectModel;
using System.IO;
using CommunityToolkit.Mvvm.ComponentModel;
using CommunityToolkit.Mvvm.Input;
using DocumentFormat.OpenXml.Bibliography;
using Microsoft.Extensions.DependencyInjection;
using SchedulePlanner.Cli;
using SchedulePlanner.Core;
using SchedulePlanner.ImportExport;
using SchedulePlanner.Wpf.Services;

namespace SchedulePlanner.Wpf.ViewModels;

public partial class SettingEntry : ObservableObject
{
    [ObservableProperty] private string _key;
    [ObservableProperty] private double _value;
    public SettingEntry(string key, double value) { Key = key; Value = value; }
}

public partial class ResultRow : ObservableObject
{
    public string? Teacher { get; set; }
    public string? Class { get; set; }
    public string? Room { get; set; }
    public string? Day { get; set; }
    public int Block { get; set; }
}

public partial class MainViewModel : ObservableObject
{
    private readonly IDialogService _dialogService;
    private readonly IServiceScopeFactory _serviceScopeFactory;

    [ObservableProperty] private string _statusMessage = "Ready.";
    [ObservableProperty] private bool _isBusy;
    [ObservableProperty] private bool _isSolving;
    [ObservableProperty] private double _jobProgress;
    [ObservableProperty] private string _temporalStatus = "Idle";
    [ObservableProperty] private SchedulerOptions _schedulerOptions = new();
    [ObservableProperty] private ScheduleResult? _scheduleResult;

    // New Collections
    public ObservableCollection<SettingEntry> Settings { get; } = new();
    public ObservableCollection<ResultRow> Results { get; } = new();

    public MainViewModel(IDialogService dialogService, IServiceScopeFactory serviceScopeFactory)
    {
        _dialogService = dialogService;
        _serviceScopeFactory = serviceScopeFactory;
        LoadDefaultSettings();
    }

    private void LoadDefaultSettings()
    {
        Settings.Add(new SettingEntry("RoomChangePenalty", 10));
        Settings.Add(new SettingEntry("ScheduleSpreadPenalty", 5));
        Settings.Add(new SettingEntry("WeekDistributionPenalty", 1));
        Settings.Add(new SettingEntry("ClassDayClusteringPenalty", 1));
        Settings.Add(new SettingEntry("ClassBlockConsistencyPenalty", 1));
        Settings.Add(new SettingEntry("StreamFragmentationPenalty", 1));
        Settings.Add(new SettingEntry("SharedRoomChangePenalty", 5));
        Settings.Add(new SettingEntry("TargetLoadAdherencePenalty", 2));
        Settings.Add(new SettingEntry("StudentRoomTransitionPenalty", 2));
        Settings.Add(new SettingEntry("FreeTimePenalty", 1));
        Settings.Add(new SettingEntry("MergedBlockConsistencyPenalty", 1));
        Settings.Add(new SettingEntry("CommonPlanningPenalty", 1));
        Settings.Add(new SettingEntry("SolverTimeLimitSeconds", 60));
        Settings.Add(new SettingEntry("BlocksPerDay", 9));
    }

    [RelayCommand]
    internal async Task ExportSettingsAsync() => await HandleExport("Settings_Export.xlsx", SettingsExport);

    [RelayCommand]
    internal async Task ExportResultsAsync() => await HandleExport("Schedule_Results.xlsx", ScheduleExport);

    private async Task<string> SettingsExport(ExportService exporter, string path)
    {
        return await exporter.ExportTemplateAsync(SchedulerOptions, path, addTimestamp: false);
    }

    private async Task<string> ScheduleExport(ExportService exporter, string path)
    {
        var exportOptions = new ScheduleResultExportOptions
        {
            ScheduleResult = ScheduleResult ?? throw new InvalidOperationException("No schedule result available."),
            FilePath = Path.GetFileName(path) ?? string.Empty
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
        IsBusy = true;
        IsSolving = true;
        TemporalStatus = "Running Solver";
        Results.Clear();
        JobProgress = 0;

        using var scope = _serviceScopeFactory.CreateScope();
        var runner = scope.ServiceProvider.GetRequiredService<SchedulingService>();

        var result = await runner.RunAsync();
        ScheduleResult = result;

        // TODO add result data

        IsBusy = false;
        IsSolving = false;
        TemporalStatus = "Idle";
        StatusMessage = "Solve complete. View results in the Results tab.";
    }

    [RelayCommand]
    internal async Task RunDemoAsync()
    {
        if (IsBusy) return;

        IsBusy = true;
        IsSolving = true;
        StatusMessage = "Loading demo configuration...";
        TemporalStatus = "Loading Demo";

        try
        {
            // Load demo options into settings
            var demoOptions = DemoDataFactory.CreateLargeK12SchoolDemo();
            
            Settings.Clear();
            Settings.Add(new SettingEntry("RoomChangePenalty", demoOptions.RoomChangePenalty));
            Settings.Add(new SettingEntry("ScheduleSpreadPenalty", demoOptions.ScheduleSpreadPenalty));
            Settings.Add(new SettingEntry("WeekDistributionPenalty", demoOptions.WeekDistributionPenalty));
            Settings.Add(new SettingEntry("ClassDayClusteringPenalty", demoOptions.ClassDayClusteringPenalty));
            Settings.Add(new SettingEntry("ClassBlockConsistencyPenalty", demoOptions.ClassBlockConsistencyPenalty));
            Settings.Add(new SettingEntry("StreamFragmentationPenalty", demoOptions.StreamFragmentationPenalty));
            Settings.Add(new SettingEntry("SharedRoomChangePenalty", demoOptions.SharedRoomChangePenalty));
            Settings.Add(new SettingEntry("TargetLoadAdherencePenalty", demoOptions.TargetLoadAdherencePenalty));
            Settings.Add(new SettingEntry("StudentRoomTransitionPenalty", demoOptions.StudentRoomTransitionPenalty));
            Settings.Add(new SettingEntry("FreeTimePenalty", demoOptions.FreeTimePenalty));
            Settings.Add(new SettingEntry("MergedBlockConsistencyPenalty", demoOptions.MergedBlockConsistencyPenalty));
            Settings.Add(new SettingEntry("CommonPlanningPenalty", demoOptions.CommonPlanningPenalty));
            Settings.Add(new SettingEntry("SolverTimeLimitSeconds", demoOptions.SolverTimeLimitSeconds));
            Settings.Add(new SettingEntry("BlocksPerDay", demoOptions.BlocksPerDay));

            await Task.Delay(500);

            StatusMessage = "Running demo scheduler (Large K12 School)...";
            JobProgress = 0;

            using var scope = _serviceScopeFactory.CreateScope();
            var runner = scope.ServiceProvider.GetRequiredService<DemoScheduleRunner>();

            var result = await runner.RunAsync();
            ScheduleResult = result;

            Results.Clear();
            
            if (result.HasSolution && result.TeacherSchedules != null)
            {
                foreach (var teacherSchedule in result.TeacherSchedules)
                {
                    foreach (var daySchedule in teacherSchedule.Days)
                    {
                        foreach (var blockSchedule in daySchedule.Blocks)
                        {
                            if (!blockSchedule.IsFree && !string.IsNullOrEmpty(blockSchedule.ClassName))
                            {
                                Results.Add(new ResultRow
                                {
                                    Teacher = teacherSchedule.TeacherName,
                                    Class = blockSchedule.ClassName ?? string.Empty,
                                    Room = blockSchedule.Room ?? string.Empty,
                                    Day = daySchedule.Day.ToString(),
                                    Block = blockSchedule.Block
                                });
                            }
                        }
                    }
                }
            }
            
            StatusMessage = result.HasSolution 
                ? $"Demo complete. Generated schedule for {result.TeacherSchedules?.Count ?? 0} teachers." 
                : $"Demo finished (no solution). Status: {result.Status}";
        }
        catch (Exception ex)
        {
            IsBusy = false;
            IsSolving = false;
            TemporalStatus = "Idle";
            StatusMessage = "Demo failed. See error.";
            _dialogService.ShowError("Demo Failed", ex.Message);
        }
        finally
        {
            IsBusy = false;
            IsSolving = false;
            TemporalStatus = "Idle";
        }
    }
}
