using System.Windows;
using System.Windows.Controls;

namespace SchedulePlanner.Wpf.Views;

public partial class MainView : UserControl
{
    public MainView()
    {
        InitializeComponent();

        RevealPasswordToggle.Checked += RevealPasswordToggle_OnChecked;
        RevealPasswordToggle.Unchecked += RevealPasswordToggle_OnUnchecked;
    }

    private void PasswordBox_OnPasswordChanged(object sender, RoutedEventArgs e)
    {
        if (DataContext is ViewModels.MainViewModel vm && sender is PasswordBox box)
        {
            vm.WorkbookPassword = box.Password;
            if (PasswordRevealBox.Visibility == Visibility.Visible)
            {
                PasswordRevealBox.Text = box.Password;
            }
        }
    }

    private void RevealPasswordToggle_OnChecked(object sender, RoutedEventArgs e)
    {
        PasswordRevealBox.Text = PasswordBox.Password;
        PasswordBox.Visibility = Visibility.Collapsed;
        PasswordRevealBox.Visibility = Visibility.Visible;
    }

    private void RevealPasswordToggle_OnUnchecked(object sender, RoutedEventArgs e)
    {
        PasswordBox.Password = PasswordRevealBox.Text;
        PasswordRevealBox.Visibility = Visibility.Collapsed;
        PasswordBox.Visibility = Visibility.Visible;
    }
}