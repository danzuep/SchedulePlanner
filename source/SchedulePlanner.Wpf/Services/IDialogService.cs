namespace SchedulePlanner.Wpf.Services;

public interface IDialogService
{
    string? OpenPdfFile();
    string? SavePdfFile();
    void ShowMessage(string title, string message);
    void ShowError(string title, string message);
}