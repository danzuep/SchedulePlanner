using System.Diagnostics;
using System.IO.Abstractions;
using System.Text;
using ClosedXML.Excel;
using SchedulePlanner.Core;

namespace SchedulePlanner.ImportExport.Excel;

public class ExcelSchedulerConfigWriter
{
    private readonly IFileSystem _fileSystem;

    public ExcelSchedulerConfigWriter(IFileSystem? fileSystem = null)
    {
        _fileSystem = fileSystem ?? new FileSystem();
    }

    public string WriteScheduleResult(
        ScheduleResult data,
        string filePath,
        bool addTimestamp = false)
    {
        if (data == null || string.IsNullOrWhiteSpace(filePath))
        {
            return string.Empty;
        }

        using var workbook = new XLWorkbook();

        AddSummaryWorksheet(workbook, data);

        foreach (var teacher in data.TeacherSchedules)
        {
            var weekSchedule = teacher.ToWeekSchedule();
            AddWorksheet(workbook, weekSchedule.Blocks, $"{teacher.TeacherName}");
        }

        var fullPath = GetFullPath(filePath, addTimestamp);
        workbook.SaveAs(fullPath);
        return fullPath;
    }

    public string WriteSchedulerOptions(SchedulerOptions data, string filePath, bool addTimestamp = false)
    {
        if (data == null || string.IsNullOrWhiteSpace(filePath))
        {
            return string.Empty;
        }

        using var workbook = new XLWorkbook();

        AddSettingsWorksheet(workbook, data);
        var teachersDto = data.Teachers.Select(t => new TeacherDto(t)).ToArray();
        AddWorksheet(workbook, teachersDto, nameof(data.Teachers));
        AddWorksheet(workbook, data.Classes, nameof(data.Classes));

        var fullPath = GetFullPath(filePath, addTimestamp);
        workbook.SaveAs(fullPath);
        return fullPath;
    }

    private void AddSummaryWorksheet(XLWorkbook workbook, ScheduleResult data)
    {
        var summaryItems = new List<SummaryItem>
        {
            new("Status", data.Status),
            new("HasSolution", data.HasSolution.ToString()),
            new("ObjectiveValue", data.ObjectiveValue?.ToString() ?? "N/A"),
            new("TotalClasses", data.Classes.Count.ToString()),
            new("TotalTeachers", data.TeacherSchedules.Count.ToString()),
            new("TotalRoomChanges", data.RoomChanges.Count.ToString()),
            new("ScheduledBlocks", data.Classes.Sum(c => c.ScheduledBlocks).ToString()),
            new("RequiredBlocks", data.Classes.Sum(c => c.RequiredBlocks).ToString()),
        };

        summaryItems.AddRange(data.SolverStatistics);

        AddWorksheet(workbook, summaryItems, "Summary");
    }

    private void AddSettingsWorksheet(XLWorkbook workbook, SchedulerOptions data)
    {
        var metadata = new Dictionary<string, XLCellValue>
        {
            [nameof(data.BlocksPerDay)] = data.BlocksPerDay,
            [nameof(data.RoomChangePenalty)] = data.RoomChangePenalty,
            [nameof(data.ScheduleSpreadPenalty)] = data.ScheduleSpreadPenalty,
            [nameof(data.WeekDistributionPenalty)] = data.WeekDistributionPenalty,
            [nameof(data.ClassDayClusteringPenalty)] = data.ClassDayClusteringPenalty,
            [nameof(data.ClassBlockConsistencyPenalty)] = data.ClassBlockConsistencyPenalty,
            [nameof(data.SolverTimeLimitSeconds)] = data.SolverTimeLimitSeconds,
        };
        AddWorksheet(workbook, metadata, SchedulerOptions.SettingsName);
    }

    private void AddWorksheet<T>(IXLWorkbook workbook, IEnumerable<T> data, string name)
    {
        var ws = workbook.AddWorksheet(name);
        ws.FirstCell().InsertTable(data, name);
        ws.Columns().AdjustToContents();
    }

    private string GetFullPath(string filePath, bool addTimestamp)
    {
        var fileInfo = new FileInfo(filePath);
        if (fileInfo.Directory != null && !fileInfo.Directory.Exists)
        {
            fileInfo.Directory.Create();
        }

        var fullPath = fileInfo.FullName;
        if (addTimestamp || IsFileLocked(fileInfo))
        {
            var fileName = new StringBuilder(Path.GetFileNameWithoutExtension(filePath));
            fileName.Append(DateTime.Now.ToDateTimeName("_"));
            fileName.Append(Path.GetExtension(filePath));
            var directory = Path.GetDirectoryName(filePath) ?? string.Empty;
            fullPath = Path.Combine(directory, fileName.ToString());
        }

        return fullPath;
    }

    private static bool IsFileLocked(FileInfo file)
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