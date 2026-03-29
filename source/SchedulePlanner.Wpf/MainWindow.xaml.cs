using System.Reflection;
using System.Windows;

namespace SchedulePlanner.Wpf
{
    /// <summary>
    /// Interaction logic for MainWindow.xaml
    /// </summary>
    public partial class MainWindow : Window
    {
        public MainWindow()
        {
            InitializeComponent();
            var version = Assembly.GetExecutingAssembly().GetName().Version ?? new Version(1, 0, 0);
            Title += $" - Version {version.Major}.{version.Minor}.{version.Build}";
        }
    }
}