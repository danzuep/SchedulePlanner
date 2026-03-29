using SchedulePlanner.Core;
using SchedulePlanner.ImportExport.Excel;

public static partial class Program
{
    public sealed class ImportService : IService
    {
        private readonly IExcelSchedulerConfigBuilder _builder;

        public ImportService(IExcelSchedulerConfigBuilder builder)
        {
            _builder = builder;
        }

        public async Task RunAsync(CancellationToken cancellationToken = default)
        {
            var schedulerConfig = await _builder.BuildAsync(cancellationToken).ConfigureAwait(false);
            var schedulingService = new SchedulingService(schedulerConfig);
            await schedulingService.RunAsync(cancellationToken).ConfigureAwait(false);
        }
    }
}