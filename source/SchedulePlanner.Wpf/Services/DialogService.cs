using System.Windows;
using Microsoft.Win32;

namespace SchedulePlanner.Wpf.Services;

public sealed class DialogService : IDialogService
{
    public string? OpenPdfFile()
    {
        var dialog = new OpenFileDialog
        {
            Filter = "PDF files (*.pdf)|*.pdf|All files (*.*)|*.*",
            Title = "Select PDF file"
        };

        return dialog.ShowDialog() == true ? dialog.FileName : null;
    }

    public string? SavePdfFile()
    {
        var dialog = new SaveFileDialog
        {
            Filter = "PDF files (*.pdf)|*.pdf|All files (*.*)|*.*",
            Title = "Save unlocked PDF as"
        };

        return dialog.ShowDialog() == true ? dialog.FileName : null;
    }

    public void ShowMessage(string title, string message)
    {
        MessageBox.Show(message, title, MessageBoxButton.OK, MessageBoxImage.Information);
    }

    public void ShowError(string title, string message)
    {
        MessageBox.Show(message, title, MessageBoxButton.OK, MessageBoxImage.Error);
    }
}