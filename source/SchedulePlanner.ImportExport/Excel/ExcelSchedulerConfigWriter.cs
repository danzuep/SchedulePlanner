using System.Diagnostics;
using System.Text;
using ClosedXML.Excel;
using SchedulePlanner.Core;

namespace SchedulePlanner.ImportExport.Excel;

public static class ExcelSchedulerConfigWriter
{
    public static string WriteWorkbook(this ScheduleResult data, string filePath, bool addTimestamp = false)
    {
        if (data == null || string.IsNullOrWhiteSpace(filePath))
        {
            return string.Empty;
        }

        using var workbook = new XLWorkbook();

        foreach (var schedule in data.TeacherSchedules)
        {
            foreach (var day in schedule.Days)
            {
                workbook.AddWorksheet(day.Blocks, $"{schedule.TeacherName}-{day.Day}");
            }
        }

        var fileInfo = new FileInfo(filePath);
        if (fileInfo.Directory != null && !fileInfo.Directory.Exists)
        {
            fileInfo.Directory.Create();
        }

        var fullPath = fileInfo.FullName;
        if (addTimestamp || fileInfo.IsFileLocked())
        {
            var fileName = new StringBuilder(Path.GetFileNameWithoutExtension(filePath));
            fileName.Append(DateTime.Now.ToDateTimeName("_"));
            fileName.Append(Path.GetExtension(filePath));
            var directory = Path.GetDirectoryName(filePath) ?? string.Empty;
            fullPath = Path.Combine(directory, fileName.ToString());
        }

        workbook.SaveAs(fullPath);
        return fullPath;
    }

    public static string WriteWorkbook(this SchedulerOptions data, string filePath, bool addTimestamp = false)
    {
        if (data == null || string.IsNullOrWhiteSpace(filePath))
        {
            return string.Empty;
        }

        using var workbook = new XLWorkbook();

        workbook.AddSettingsWorksheet(data);
        workbook.AddWorksheet(data.Teachers, nameof(data.Teachers));
        workbook.AddWorksheet(data.Classes, nameof(data.Classes));
        workbook.AddWorksheet(data.Departments, nameof(data.Departments));
        workbook.AddWorksheet(data.TeacherDepartments, nameof(data.TeacherDepartments));

        var fileInfo = new FileInfo(filePath);
        if (fileInfo.Directory != null && !fileInfo.Directory.Exists)
        {
            fileInfo.Directory.Create();
        }

        var fullPath = fileInfo.FullName;
        if (addTimestamp || fileInfo.IsFileLocked())
        {
            var fileName = new StringBuilder(Path.GetFileNameWithoutExtension(filePath));
            fileName.Append(DateTime.Now.ToDateTimeName("_"));
            fileName.Append(Path.GetExtension(filePath));
            var directory = Path.GetDirectoryName(filePath) ?? string.Empty;
            fullPath = Path.Combine(directory, fileName.ToString());
        }

        workbook.SaveAs(fullPath);
        return fullPath;
    }

    private static void AddSettingsWorksheet(this XLWorkbook workbook, SchedulerOptions data)
    {
        var metadata = new Dictionary<string, XLCellValue>
        {
            [nameof(data.BlocksPerDay)] = data.BlocksPerDay,
            [nameof(data.RoomChangePenalty)] = data.RoomChangePenalty,
            [nameof(data.SolverTimeLimitSeconds)] = data.SolverTimeLimitSeconds,
        };
        workbook.AddWorksheet(metadata, SchedulerOptions.SettingsName);
    }

    public static void AddWorksheet<T>(this IXLWorkbook workbook, IEnumerable<T> data, string name)
    {
        var ws = workbook.AddWorksheet(name);
        ws.FirstCell().InsertTable(data, name);
        ws.Columns().AdjustToContents();
    }

    public static bool IsFileLocked(this FileInfo file)
    {
        try
        {
            using var stream = file.Open(FileMode.OpenOrCreate, FileAccess.Read, FileShare.None);
            stream.Close();
            return false;
        }
        catch
        {
            Debug.WriteLine($"The file '{file.FullName}' is currently in use. Please close it and try again.");
            return true;
        }
    }
}