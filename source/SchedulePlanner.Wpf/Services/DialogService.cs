using System.IO;
using System.Windows;
using Microsoft.Win32;

namespace SchedulePlanner.Wpf.Services;

public sealed class DialogService : IDialogService
{
    public string? OpenFile()
    {
        var dialog = new OpenFileDialog
        {
            Filter = "Excel files (*.xlsx)|*.xlsx|All files (*.*)|*.*",
            Title = "Select Excel file"
        };

        return dialog.ShowDialog() == true ? dialog.FileName : null;
    }

    public string? SaveFile(string? defaultPath = null)
    {
        var dialog = new SaveFileDialog
        {
            Filter = "Excel files (*.xlsx)|*.xlsx|All files (*.*)|*.*",
            Title = "Save processed Excel file as"
        };

        if (!string.IsNullOrWhiteSpace(defaultPath))
        {
            dialog.InitialDirectory = Path.GetDirectoryName(defaultPath);
            dialog.FileName = Path.GetFileName(defaultPath);
        }

        return dialog.ShowDialog() == true ? dialog.FileName : null;
    }

    public string? SelectFolder()
    {
        var dialog = new OpenFolderDialog
        {
            Title = "Choose a folder to save the Excel template file",
            Multiselect = false
        };

        return dialog.ShowDialog() == true ? dialog.FolderName : null;
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