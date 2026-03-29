using System.Globalization;
using ClosedXML.Excel;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using SchedulePlanner.Core;

namespace SchedulePlanner.ImportExport.Excel;

public interface IExcelSchedulerConfigReader
{
    Task<SchedulerConfig> BuildAsync(CancellationToken cancellationToken = default);
}

public sealed class ExcelSchedulerConfigReader : IExcelSchedulerConfigReader
{
    private readonly ImportExportConfig _options;
    private readonly ILogger<ExcelSchedulerConfigReader> _logger;

    public ExcelSchedulerConfigReader(
        IOptions<ImportExportConfig> options,
        ILogger<ExcelSchedulerConfigReader> logger)
    {
        _options = options?.Value ?? throw new ArgumentNullException(nameof(options));
        _logger = logger ?? throw new ArgumentNullException(nameof(logger));
    }

    public Task<SchedulerConfig> BuildAsync(CancellationToken cancellationToken = default)
    {
        var fullPath = Path.GetFullPath(_options.FilePath);
        if (!File.Exists(fullPath))
        {
            throw new FileNotFoundException($"Excel file '{fullPath}' not found.");
        }

        using var workbook = new XLWorkbook(fullPath);

        var config = new SchedulerConfig
        {
            Teachers = ReadTeachers(workbook),
            Classes = ReadClasses(workbook),
            Departments = ReadDepartments(workbook),
            TeacherDepartments = ReadTeacherDepartments(workbook),
            Days = ReadDays(workbook)
        };

        // Optional scalar settings from a "Scheduler" sheet
        ReadSchedulerSettings(workbook, config);

        _logger.LogInformation(
            "Loaded Excel scheduler config from {File}. Teachers: {Teachers}, Classes: {Classes}",
            _options.FileName,
            config.Teachers.Count,
            config.Classes.Count);

        return Task.FromResult(config);
    }

    private static List<Teacher> ReadTeachers(XLWorkbook workbook)
    {
        var ws = workbook.Worksheet("Teachers");
        return ReadRows(ws, row => new Teacher
        {
            Id = row.GetString("Id"),
            FullName = row.GetString("FullName"),
            PreferredRoom = row.GetString("PreferredRoom"),
            TargetLoadBlocks = row.GetInt("TargetLoadBlocks", 10)
        });
    }

    private static List<Class> ReadClasses(XLWorkbook workbook)
    {
        var ws = workbook.Worksheet("Classes");
        return ReadRows(ws, row => new Class
        {
            Key = row.GetString("Key"),
            Department = row.GetString("Department"),
            Name = row.GetString("Name"),
            PreferredRoom = row.GetString("PreferredRoom"),
            WeeklyBlocks = row.GetInt("WeeklyBlocks", 1)
        });
    }

    private static List<Department> ReadDepartments(XLWorkbook workbook)
    {
        var ws = workbook.Worksheet("Departments");
        return ReadRows(ws, row => new Department
        {
            Key = row.GetString("Key"),
            Name = row.GetString("Name")
        });
    }

    private static List<TeacherDepartment> ReadTeacherDepartments(XLWorkbook workbook)
    {
        var ws = workbook.Worksheet("TeacherDepartments");
        return ReadRows(ws, row => new TeacherDepartment
        {
            TeacherId = row.GetString("TeacherId"),
            Department = row.GetString("Department")
        });
    }

    private static IReadOnlyList<DayOfWeek> ReadDays(XLWorkbook workbook)
    {
        if (!workbook.TryGetWorksheet("Days", out var ws))
        {
            return new[]
            {
                DayOfWeek.Monday,
                DayOfWeek.Tuesday,
                DayOfWeek.Wednesday,
                DayOfWeek.Thursday,
                DayOfWeek.Friday
            };
        }

        var days = new List<DayOfWeek>();
        foreach (var row in ws.RowsUsed().Skip(1))
        {
            var text = row.Cell(1).GetString();
            if (Enum.TryParse<DayOfWeek>(text, true, out var day))
            {
                days.Add(day);
            }
        }

        return days.Count > 0 ? days : new[]
        {
            DayOfWeek.Monday,
            DayOfWeek.Tuesday,
            DayOfWeek.Wednesday,
            DayOfWeek.Thursday,
            DayOfWeek.Friday
        };
    }

    private static void ReadSchedulerSettings(XLWorkbook workbook, SchedulerConfig config)
    {
        if (!workbook.TryGetWorksheet("Settings", out var ws))
        {
            return;
        }

        foreach (var row in ws.RowsUsed().Skip(1))
        {
            var key = row.Cell(1).GetString();
            var value = row.Cell(2).GetString();

            switch (key)
            {
                case "BlocksPerDay":
                    if (int.TryParse(value, out var blocks))
                        config.BlocksPerDay = blocks;
                    break;

                case "RoomChangePenalty":
                    if (int.TryParse(value, out var penalty))
                        config.RoomChangePenalty = penalty;
                    break;

                case "SolverTimeLimitSeconds":
                    if (double.TryParse(value, NumberStyles.Any, CultureInfo.InvariantCulture, out var limit))
                        config.SolverTimeLimitSeconds = limit;
                    break;
            }
        }
    }

    private static List<T> ReadRows<T>(IXLWorksheet ws, Func<RowReader, T> projector)
    {
        var rows = new List<T>();
        var headerRow = ws.Row(1);
        var headers = headerRow.CellsUsed()
            .Select((c, i) => (Name: c.GetString().Trim(), Index: i + 1))
            .ToDictionary(x => x.Name, x => x.Index, StringComparer.OrdinalIgnoreCase);

        foreach (var row in ws.RowsUsed().Skip(1))
        {
            if (row.IsEmpty())
                continue;

            rows.Add(projector(new RowReader(row, headers)));
        }

        return rows;
    }

    private sealed class RowReader
    {
        private readonly IXLRow _row;
        private readonly IReadOnlyDictionary<string, int> _headers;

        public RowReader(IXLRow row, IReadOnlyDictionary<string, int> headers)
        {
            _row = row;
            _headers = headers;
        }

        public string GetString(string columnName, string defaultValue = "")
        {
            return _headers.TryGetValue(columnName, out var index)
                ? _row.Cell(index).GetString().Trim()
                : defaultValue;
        }

        public int GetInt(string columnName, int defaultValue = 0)
        {
            var text = GetString(columnName);
            return int.TryParse(text, NumberStyles.Integer, CultureInfo.InvariantCulture, out var value)
                ? value
                : defaultValue;
        }
    }
}