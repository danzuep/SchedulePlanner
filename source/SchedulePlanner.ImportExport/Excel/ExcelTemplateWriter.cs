using System.Text;
using ClosedXML.Excel;
using SchedulePlanner.Core;

namespace SchedulePlanner.ImportExport.Excel;

public static class ExcelTemplateWriter
{
    public static string WriteTemplate(ImportExportConfig importExportConfig)
    {
        var schedulerConfig = CreateDefaultSchedulerConfig();
        var filePath = Path.Combine(importExportConfig.ImportDirectory, importExportConfig.ImportFileName);
        var fullPath = WriteWorkbook(schedulerConfig, filePath);
        return fullPath;
    }

    public static string WriteWorkbook(this SchedulerConfig data, string filePath)
    {
        if (data == null || string.IsNullOrWhiteSpace(filePath))
        {
            return string.Empty;
        }

        using var workbook = new XLWorkbook();

        workbook.AddSettingsWorksheet(data);
        workbook.InsertWorksheetTable(data.Teachers, nameof(data.Teachers));
        workbook.InsertWorksheetTable(data.Classes, nameof(data.Classes));
        workbook.InsertWorksheetTable(data.Departments, nameof(data.Departments));
        workbook.InsertWorksheetTable(data.TeacherDepartments, nameof(data.TeacherDepartments));

        var fileName = new StringBuilder(Path.GetFileNameWithoutExtension(filePath));
        fileName.Append("_");
        fileName.Append(DateTime.Now.ToDateTimeName());
        fileName.Append(Path.GetExtension(filePath));
        var directory = Path.GetDirectoryName(filePath) ?? string.Empty;
        var fullPath = Path.Combine(directory, fileName.ToString());

        var fileInfo = new FileInfo(fullPath);
        if (fileInfo.Directory != null && !fileInfo.Directory.Exists)
        {
            fileInfo.Directory.Create();
        }

        if (fileInfo.IsFileLocked())
        {
            throw new IOException($"The file '{fileInfo.FullName}' is currently in use. Please close it and try again.");
        }

        workbook.SaveAs(fileInfo.FullName);
        return fileInfo.FullName;
    }

    private static void AddSettingsWorksheet(this XLWorkbook workbook, SchedulerConfig data)
    {
        var ws = workbook.Worksheets.Add("Settings");

        var metadata = new Dictionary<string, XLCellValue>
        {
            [nameof(data.BlocksPerDay)] = data.BlocksPerDay,
            [nameof(data.RoomChangePenalty)] = data.RoomChangePenalty,
            [nameof(data.SolverTimeLimitSeconds)] = data.SolverTimeLimitSeconds,
        };

        ws.AddKeyValueTable(metadata);

        ws.Row(1).Style.Font.Bold = true;

        ws.Columns().AdjustToContents();
    }

    public static SchedulerConfig CreateDefaultSchedulerConfig()
    {
        return new SchedulerConfig
        {
            BlocksPerDay = 9,
            RoomChangePenalty = 3,
            SolverTimeLimitSeconds = 15.0,
            Teachers = new List<Teacher>
            {
                new Teacher
                {
                    Id = "1",
                    FullName = "Adams",
                    PreferredRoom = "601",
                    TargetLoadBlocks = 12
                },
                new Teacher
                {
                    Id = "2",
                    FullName = "Bennett",
                    PreferredRoom = "602",
                    TargetLoadBlocks = 11
                },
                new Teacher
                {
                    Id = "3",
                    FullName = "Choi",
                    PreferredRoom = "603",
                    TargetLoadBlocks = 10
                },
                new Teacher
                {
                    Id = "4",
                    FullName = "Delgado",
                    PreferredRoom = "604",
                    TargetLoadBlocks = 9
                }
            },
                Departments = new List<Department>
            {
                new Department { Key = "MATH", Name = "Mathematics" },
                new Department { Key = "SCI", Name = "Science" },
                new Department { Key = "LANG", Name = "Language Arts" },
                new Department { Key = "HIST", Name = "History" }
            },
                TeacherDepartments = new List<TeacherDepartment>
            {
                new TeacherDepartment { TeacherId = "1", Department = "MATH" },
                new TeacherDepartment { TeacherId = "2", Department = "SCI" },
                new TeacherDepartment { TeacherId = "3", Department = "LANG" },
                new TeacherDepartment { TeacherId = "4", Department = "HIST" }
            },
                Classes = new List<Class>
            {
                new Class
                {
                    Key = "MATH10A",
                    Department = "MATH",
                    Name = "Algebra I",
                    PreferredRoom = "601",
                    WeeklyBlocks = 5
                },
                new Class
                {
                    Key = "MATH11B",
                    Department = "MATH",
                    Name = "Geometry",
                    PreferredRoom = "602",
                    WeeklyBlocks = 4
                },
                new Class
                {
                    Key = "SCI11A",
                    Department = "SCI",
                    Name = "Physics",
                    PreferredRoom = "601",
                    WeeklyBlocks = 4
                },
                new Class
                {
                    Key = "SCI12B",
                    Department = "SCI",
                    Name = "Chemistry",
                    PreferredRoom = "603",
                    WeeklyBlocks = 4
                },
                new Class
                {
                    Key = "LANG10A",
                    Department = "LANG",
                    Name = "English Literature",
                    PreferredRoom = "601",
                    WeeklyBlocks = 3
                },
                new Class
                {
                    Key = "HIST10A",
                    Department = "HIST",
                    Name = "World History",
                    PreferredRoom = "604",
                    WeeklyBlocks = 3
                }
            }
        };
    }
}