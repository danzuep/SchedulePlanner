using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using SchedulePlanner.Core;

public static class ServiceCollectionExtensions
{
    public static IServiceCollection AddSchedulingService(this IServiceCollection services, IConfiguration configuration)
    {
        if (services == null)
        {
            throw new ArgumentNullException(nameof(services));
        }
        if (configuration == null)
        {
            throw new ArgumentNullException(nameof(configuration));
        }
        var config = configuration.GetSection(SchedulerConfig.SectionName);
        services.Configure<SchedulerConfig>(config);
        services.AddSingleton<IService, SchedulingService>();
        services.AddHostedService<Worker>();
        return services;
    }
}
