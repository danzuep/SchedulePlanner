using System.Diagnostics.CodeAnalysis;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using SchedulePlanner.Core;
using SchedulePlanner.ImportExport.Excel;

namespace SchedulePlanner.Worker
{
    [ExcludeFromCodeCoverage]
    public static class Program
    {
        public static async Task Main(string[] args)
        {
            using var host = Host.CreateDefaultBuilder()
                .InitialiseBuilderDefaults()
                .ConfigureServices(Initialise)
                .Build();
            await host.RunAsync();

            Console.WriteLine("Press any key to exit...");
            Console.ReadKey();
        }

        public static void Initialise(HostBuilderContext context, IServiceCollection services)
        {
            services.AddSingleton<IService, ImportService>();
            services.AddHostedService<Worker>();
        }

        public sealed class Worker : BackgroundService
        {
            private readonly IService _processExecutionService;

            public Worker(IService processExecutionService)
            {
                _processExecutionService = processExecutionService;
            }

            protected override async Task ExecuteAsync(CancellationToken cancellationToken)
            {
                await _processExecutionService.RunAsync(cancellationToken).ConfigureAwait(false);
            }
        }
    }
}
