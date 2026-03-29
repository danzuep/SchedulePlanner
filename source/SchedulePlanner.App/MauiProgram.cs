using CommunityToolkit.Maui;
using Microsoft.Extensions.Logging;
using SchedulePlanner.App.ViewModels;
using SchedulePlanner.ImportExport;

namespace SchedulePlanner.App;

public static class MauiProgram
{
	public static MauiApp CreateMauiApp()
	{
		var builder = MauiApp.CreateBuilder();
		builder
			.UseMauiApp<App>()
			.UseMauiCommunityToolkit()
			.ConfigureFonts(fonts =>
			{
				fonts.AddFont("OpenSans-Regular.ttf", "OpenSansRegular");
				fonts.AddFont("OpenSans-Semibold.ttf", "OpenSansSemibold");
			});

#if DEBUG
		builder.Logging.AddDebug();
#endif

		builder.Services.AddSchedulingService(builder.Configuration);
        builder.Services.AddSingleton<MainViewModel>();
        builder.Services.AddTransient<MainPage>();

		return builder.Build();
	}
}
