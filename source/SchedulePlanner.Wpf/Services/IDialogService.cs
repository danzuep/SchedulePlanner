namespace SchedulePlanner.Wpf.Services;

public interface IDialogService
{
    string? OpenFile();
    string? SaveFile(string? defaultPath = null);
    void ShowMessage(string title, string message);
    void ShowError(string title, string message);
}