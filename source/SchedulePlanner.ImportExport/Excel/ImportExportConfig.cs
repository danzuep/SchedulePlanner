using Microsoft.Extensions.Options;

namespace SchedulePlanner.ImportExport.Excel;

public sealed record ImportExportConfig : IOptions<ImportExportConfig>
{
    public ImportExportConfig Value => this;

    public static readonly string SectionName = "ImportExport";

    public ImportExportFileType FileType { get; set; } = ImportExportFileType.Xlsx;

    public string ImportDirectory { get; set; } = string.Empty;

    public string ImportFileName { get; set; } = string.Empty;
}