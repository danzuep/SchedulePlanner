using Microsoft.Extensions.Options;

namespace SchedulePlanner.ImportExport.Excel;

public sealed record ImportExportConfig : IOptions<ImportExportConfig>
{
    public ImportExportConfig Value => this;

    public static readonly string SectionName = "ImportExport";

    public static readonly ImportExportConfig Default = new ImportExportConfig
    {
#if DEBUG
        Directory = "../..",
#endif
        FileName = "schedule.xlsx"
    };

    public ImportExportFileType FileType { get; set; } = ImportExportFileType.Xlsx;

    public string Directory { get; set; } = string.Empty;

    public string FileName { get; set; } = string.Empty;

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