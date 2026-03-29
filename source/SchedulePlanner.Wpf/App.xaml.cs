using System.Windows;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using SchedulePlanner.ImportExport;
using SchedulePlanner.ImportExport.Excel;
using SchedulePlanner.Wpf.Services;
using SchedulePlanner.Wpf.ViewModels;

namespace SchedulePlanner.Wpf
{
    public partial class App : Application
    {
        public IServiceProvider Services { get; }

        public App()
        {
            var services = new ServiceCollection();

            services.AddLogging(builder =>
            {
                builder.SetMinimumLevel(LogLevel.Debug);
                builder.AddDebug();
                builder.AddConsole();
            });

            services.AddSingleton<IDialogService, DialogService>();
            services.AddSingleton<MainViewModel>();

            var configuration = new ConfigurationBuilder()
                .AddJsonFile("appsettings.json", optional: false, reloadOnChange: true)
                .AddEnvironmentVariables()
                .Build();

            services.AddSchedulingService(configuration);
            services.AddExcelSchedulerSources(configuration);
            services.AddScoped<ExportService>();

            Services = services.BuildServiceProvider();
        }

        protected override void OnStartup(StartupEventArgs e)
        {
            base.OnStartup(e);

            var window = new MainWindow
            {
                DataContext = Services.GetRequiredService<MainViewModel>()
            };

            MainWindow = window;
            window.Show();
        }
    }
}