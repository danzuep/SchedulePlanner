using CommunityToolkit.Mvvm.ComponentModel;
using CommunityToolkit.Mvvm.Input;
using SchedulePlanner.Core;
using System.Collections.ObjectModel;

namespace SchedulePlanner.App.ViewModels;

public partial class MainViewModel : ObservableObject
{
    public ObservableCollection<Teacher> Teachers { get; } = new();
    public ObservableCollection<Class> Classes { get; } = new();
    public ObservableCollection<TeacherDepartment> Departments { get; } = new();
    public ObservableCollection<ScheduleEntryViewModel> ScheduleEntries { get; } = new();
    public ObservableCollection<PenaltyViewModel> Penalties { get; } = new();

    [ObservableProperty] private string newTeacherName = string.Empty;
    [ObservableProperty] private string newTeacherRoom = string.Empty;
    [ObservableProperty] private int newTeacherTargetLoad = 10;

    [ObservableProperty] private string newClassKey = string.Empty;
    [ObservableProperty] private string newClassName = string.Empty;
    [ObservableProperty] private string newClassRoom = string.Empty;
    [ObservableProperty] private int newClassBlocks = 1;

    [ObservableProperty] private Teacher? selectedDepartmentTeacher;
    [ObservableProperty] private Class? selectedDepartmentClass;

    [ObservableProperty] private string resultMessage = "Build your schedule and press Generate Schedule.";
    [ObservableProperty] private bool isBusy;

    public SchedulingService? Strategy { get; set; }

    public MainViewModel()
    {
        // seed a department list for the picker so it is never empty
        Departments.CollectionChanged += (_, _) => { }; // no-op, ensures the collection exists
    }

    public Task InitializeAsync()
    {
        if (Strategy is null)
        {
            ResultMessage = "No scheduling strategy configured.";
            return Task.CompletedTask;
        }
        foreach (var teacher in Strategy.Config.Teachers)
        {
            Teachers.Add(teacher);
        }
        foreach (var classes in Strategy.Config.Classes)
        {
            Classes.Add(classes);
        }
        foreach (var department in Strategy.Config.TeacherDepartments)
        {
            Departments.Add(department);
        }
        return Task.CompletedTask;
    }

    [RelayCommand(CanExecute = nameof(CanAddTeacher))]
    private void AddTeacher()
    {
        var teacher = new Teacher
        {
            Id = Guid.NewGuid().ToString("N"),
            FullName = NewTeacherName.Trim(),
            PreferredRoom = NewTeacherRoom.Trim(),
            TargetLoadBlocks = NewTeacherTargetLoad
        };

        Teachers.Add(teacher);
        NewTeacherName = string.Empty;
        NewTeacherRoom = string.Empty;
        NewTeacherTargetLoad = 10;
        ResultMessage = $"Added teacher {teacher.FullName}.";
    }

    private bool CanAddTeacher() => !string.IsNullOrWhiteSpace(NewTeacherName);

    [RelayCommand(CanExecute = nameof(CanAddClass))]
    private void AddClass()
    {
        var cls = new Class
        {
            Key = NewClassKey.Trim(),
            Name = NewClassName.Trim(),
            PreferredRoom = NewClassRoom.Trim(),
            WeeklyBlocks = Math.Max(1, NewClassBlocks),
            Department = string.Empty // you might hook a department picker later
        };

        Classes.Add(cls);
        NewClassKey = string.Empty;
        NewClassName = string.Empty;
        NewClassRoom = string.Empty;
        NewClassBlocks = 1;
        ResultMessage = $"Added class {cls.Key}.";
    }

    private bool CanAddClass() => !string.IsNullOrWhiteSpace(NewClassKey);

    [RelayCommand(CanExecute = nameof(CanAddDepartmentLink))]
    private void AddDepartmentLink()
    {
        if (SelectedDepartmentTeacher is null || SelectedDepartmentClass is null)
        {
            return;
        }

        var link = new TeacherDepartment
        {
            TeacherId = SelectedDepartmentTeacher.Id,
            Department = SelectedDepartmentClass.Department
        };

        if (!Departments.Any(d => d.TeacherId == link.TeacherId && d.Department == link.Department))
        {
            Departments.Add(link);
            ResultMessage = $"Linked {SelectedDepartmentTeacher.FullName} to {SelectedDepartmentClass.Key}.";
        }
    }

    private bool CanAddDepartmentLink()
        => SelectedDepartmentTeacher is not null && SelectedDepartmentClass is not null;

    [RelayCommand(CanExecute = nameof(CanRunSchedule))]
    private async Task RunScheduleAsync()
    {
        if (Strategy is null)
        {
            ResultMessage = "No scheduling strategy configured.";
            return;
        }
        await Strategy.RunAsync();
    }

    private bool CanRunSchedule() => Strategy is not null && Teachers.Any() && Classes.Any();

    public record ScheduleEntryViewModel(string TeacherName, string Day, int Block, string DisplayText);
    public record PenaltyViewModel(string TeacherName, string Day, int Block, string FromClass, string ToClass);
}