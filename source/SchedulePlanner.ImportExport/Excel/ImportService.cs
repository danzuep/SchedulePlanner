using Microsoft.Extensions.Logging;
using SchedulePlanner.Core;

namespace SchedulePlanner.ImportExport.Excel
{
    public sealed class ImportService : IService
    {
        private readonly IExcelSchedulerConfigReader _builder;
        private readonly ILogger<SchedulingService>? _logger;

        public ImportService(IExcelSchedulerConfigReader builder, ILogger<SchedulingService>? logger = null)
        {
            _builder = builder;
            _logger = logger;
        }

        public async Task RunAsync(CancellationToken cancellationToken = default)
        {
            var schedulerConfig = await _builder.BuildAsync(cancellationToken).ConfigureAwait(false);
            var schedulingService = new SchedulingService(schedulerConfig, _logger);
            await schedulingService.RunAsync(cancellationToken).ConfigureAwait(false);
        }
    }
}