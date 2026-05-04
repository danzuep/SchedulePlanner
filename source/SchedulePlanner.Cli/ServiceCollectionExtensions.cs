using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using SchedulePlanner.Core;
using SchedulePlanner.ImportExport;
using SchedulePlanner.ImportExport.Excel;

namespace SchedulePlanner.Cli;

public static class ServiceCollectionExtensions
{
    public static IServiceCollection AddDemoScheduleRunner(
        this IServiceCollection services,
        IConfiguration configuration)
    {
        if (services == null) throw new ArgumentNullException(nameof(services));
        if (configuration == null) throw new ArgumentNullException(nameof(configuration));

        //services.Configure<SchedulerOptions>(configuration.GetSection(SchedulerOptions.SectionName));
        services.AddDemoScheduleServices();
        services.AddTransient<ImportService>();
        services.AddSingleton<SchedulingService>();
        services.AddSingleton<IService<ScheduleResult>>(provider => provider.GetRequiredService<SchedulingService>());
        services.AddScoped<DemoScheduleRunner>();
        //services.AddSingleton<IService<ScheduleResult>>(provider => provider.GetRequiredService<DemoScheduleRunner>());
        return services;
    }

    public static IServiceCollection AddDemoScheduleServices(
        this IServiceCollection services)
    {
        if (services == null) throw new ArgumentNullException(nameof(services));

        services.AddSingleton<ImportExportService>();
        services.AddSingleton<ExportService>();
        services.AddSingleton<ImportService>();
        services.AddSingleton<IConfigValidator, ConfigValidator>();
        services.AddSingleton<IClassAssignmentBuilder, ClassAssignmentBuilder>();
        services.AddSingleton<IConstraintBuilder, ConstraintBuilder>();
        services.AddSingleton<IOptimizationBuilder, OptimizationBuilder>();
        services.AddSingleton<IResultBuilder, ResultBuilder>();
        services.AddSingleton<IScheduleLogger, ScheduleLogger>();
        return services;
    }
}
