namespace SchedulePlanner.ImportExport;

public interface IScheduleResultExporter
{
    Task<string> ExportAsync();
}
