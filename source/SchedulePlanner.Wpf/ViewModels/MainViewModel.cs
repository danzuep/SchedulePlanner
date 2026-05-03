using System.Collections.ObjectModel;
using System.IO;
using CommunityToolkit.Mvvm.ComponentModel;
using CommunityToolkit.Mvvm.Input;
using Microsoft.Extensions.DependencyInjection;
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
    public string Teacher { get; set; }
    public string Class { get; set; }
    public string Room { get; set; }
    public string Day { get; set; }
    public int Block { get; set; }
}

public partial class MainViewModel : ObservableObject
{
    private readonly IDialogService _dialogService;
    private readonly IServiceScopeFactory _serviceScopeFactory;

    [ObservableProperty] private string _statusMessage = "Ready.";
    [ObservableProperty] private bool _isBusy;
    [ObservableProperty] private double _jobProgress;
    [ObservableProperty] private string _temporalStatus = "Idle";

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
        Settings.Add(new SettingEntry("SolverTimeLimitSeconds", 60));
    }

    [RelayCommand]
    private async Task ExportSettingsAsync() => await HandleExport("Settings_Export.xlsx");

    [RelayCommand]
    private async Task ExportResultsAsync() => await HandleExport("Schedule_Results.xlsx");

    private async Task HandleExport(string defaultName)
    {
        var path = _dialogService.SaveFile(defaultName);
        if (string.IsNullOrWhiteSpace(path)) return;

        try
        {
            IsBusy = true;
            StatusMessage = $"Exporting to {Path.GetFileName(path)}...";
            await Task.Delay(1000); // Simulate Excel Generation
            _dialogService.ShowMessage("Success", "File exported successfully.");
        }
        catch (Exception ex)
        {
            _dialogService.ShowError("Export Failed", ex.Message);
        }
        finally { IsBusy = false; StatusMessage = "Ready."; }
    }

    [RelayCommand]
    private async Task RunSolveAsync()
    {
        IsBusy = true;
        TemporalStatus = "Running Solver";
        Results.Clear();

        // Simulated Solver Progress
        for (int i = 0; i <= 100; i += 20)
        {
            JobProgress = i;
            await Task.Delay(400);
        }

        // Dummy Result Data
        Results.Add(new ResultRow { Teacher = "Smith", Class = "Math 101", Room = "Lab 1", Day = "Monday", Block = 1 });
        Results.Add(new ResultRow { Teacher = "Jones", Class = "History 2", Room = "Room 202", Day = "Monday", Block = 2 });

        IsBusy = false;
        TemporalStatus = "Idle";
        StatusMessage = "Solve complete. View results in the Results tab.";
    }
}