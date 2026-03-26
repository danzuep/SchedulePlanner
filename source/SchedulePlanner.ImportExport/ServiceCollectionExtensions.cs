using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using SchedulePlanner.Core;

namespace SchedulePlanner;

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
        services.AddSingleton<SchedulingService>();
        services.AddSingleton<IService>(provider =>
            provider.GetRequiredService<SchedulingService>());
        return services;
    }
}
