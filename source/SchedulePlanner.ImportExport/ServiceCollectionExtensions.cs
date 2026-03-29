using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using SchedulePlanner.Core;
using SchedulePlanner.ImportExport.Excel;

namespace SchedulePlanner.ImportExport;

public static class ServiceCollectionExtensions
{
    public static IServiceCollection AddSchedulingService(
        this IServiceCollection services,
        IConfiguration configuration)
    {
        if (services == null) throw new ArgumentNullException(nameof(services));
        if (configuration == null) throw new ArgumentNullException(nameof(configuration));

        services.Configure<SchedulerConfig>(configuration.GetSection(SchedulerConfig.SectionName));
        services.AddSingleton<SchedulingService>();
        services.AddSingleton<IService>(provider => provider.GetRequiredService<SchedulingService>());
        return services;
    }

    public static IServiceCollection AddExcelSchedulerSources(
        this IServiceCollection services,
        IConfiguration configuration)
    {
        if (services == null) throw new ArgumentNullException(nameof(services));
        if (configuration == null) throw new ArgumentNullException(nameof(configuration));

        services.Configure<ExcelOptions>(configuration.GetSection(ExcelOptions.SectionName));
        services.AddTransient<IExcelSchedulerConfigBuilder, ExcelSchedulerConfigBuilder>();
        return services;
    }

    //extension<IServiceCollection>(IServiceCollection services) { }
}
