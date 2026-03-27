using System.ComponentModel;
using System.Runtime.CompilerServices;
using System.Windows.Input;
using CommunityToolkit.Mvvm.Input;

namespace SchedulePlanner.Wpf.ViewModels;

public class MainViewModel : INotifyPropertyChanged
{
    private string? _inputWorkbookPath;
    private string? _outputWorkbookPath;
    private string? _workbookPassword;
    private bool _waitForClose;
    private string _statusMessage = "Ready.";

    public string? InputWorkbookPath
    {
        get => _inputWorkbookPath;
        set
        {
            if (_inputWorkbookPath != value)
            {
                _inputWorkbookPath = value;
                OnPropertyChanged();
            }
        }
    }

    public string? OutputWorkbookPath
    {
        get => _outputWorkbookPath;
        set
        {
            if (_outputWorkbookPath != value)
            {
                _outputWorkbookPath = value;
                OnPropertyChanged();
            }
        }
    }

    public string? WorkbookPassword
    {
        get => _workbookPassword;
        set
        {
            if (_workbookPassword != value)
            {
                _workbookPassword = value;
                OnPropertyChanged();
            }
        }
    }

    public bool WaitForClose
    {
        get => _waitForClose;
        set
        {
            if (_waitForClose != value)
            {
                _waitForClose = value;
                OnPropertyChanged();
            }
        }
    }

    public string StatusMessage
    {
        get => _statusMessage;
        set
        {
            if (_statusMessage != value)
            {
                _statusMessage = value;
                OnPropertyChanged();
            }
        }
    }

    public ICommand BrowseInputWorkbookCommand { get; }
    public ICommand BrowseOutputWorkbookCommand { get; }
    public ICommand ProcessWorkbookCommand { get; }

    public MainViewModel()
    {
        BrowseInputWorkbookCommand = new RelayCommand(BrowseInputWorkbook);
        BrowseOutputWorkbookCommand = new RelayCommand(BrowseOutputWorkbook);
        ProcessWorkbookCommand = new RelayCommand(ProcessWorkbook);
    }

    private void BrowseInputWorkbook()
    {
        StatusMessage = "Browse for an input Excel workbook.";
    }

    private void BrowseOutputWorkbook()
    {
        StatusMessage = "Browse for an output Excel workbook.";
    }

    private void ProcessWorkbook()
    {
        StatusMessage = "Processing workbook...";
    }

    public event PropertyChangedEventHandler? PropertyChanged;

    private void OnPropertyChanged([CallerMemberName] string? propertyName = null)
        => PropertyChanged?.Invoke(this, new PropertyChangedEventArgs(propertyName));
}