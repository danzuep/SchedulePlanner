using Microsoft.Extensions.Options;

namespace SchedulePlanner.ImportExport.Excel;

public sealed record ImportExportOptions : IOptions<ImportExportOptions>
{
    public ImportExportOptions Value => this;

    public static readonly string SectionName = "ImportExport";

    public static readonly ImportExportOptions Default = new ImportExportOptions();

    public ImportExportFileType FileType { get; set; } = ImportExportFileType.Xlsx;

    public string Directory { get; set; } =
#if DEBUG
        "../..";
#else
        ".";
#endif

    public string FileName { get; set; } = "schedule-demo.xlsx";

    public string FilePath
    {
        get => Path.Combine(Directory, FileName);
        set
        {
            Directory = Path.GetDirectoryName(value) ?? string.Empty;
            FileName = Path.GetFileName(value);
        }
    }
}

public enum ImportExportFileType
{
    Csv = 0,
    Xlsx = 1,
}