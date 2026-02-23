namespace SchedulePlanner.Core;

using System;
using System.IO.Abstractions;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;

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
        services.AddSingleton<IFileSystem, FileSystem>();
        services.AddSingleton<IService, SchedulingService>();
        services.AddHostedService<Worker>();
        return services;
    }
}
