using ClosedXML.Excel;

namespace SchedulePlanner.ImportExport.Excel;

// SchedulePlanner.Excel.ExcelTemplateWriter.WriteTemplate("schedule-template.xlsx");
public static class ExcelTemplateWriter
{
    public static void WriteTemplate(string filePath)
    {
        using var workbook = new XLWorkbook();

        WriteSchedulerSheet(workbook);
        WriteDaysSheet(workbook);
        WriteTeachersSheet(workbook);
        WriteClassesSheet(workbook);
        WriteDepartmentsSheet(workbook);
        WriteTeacherDepartmentsSheet(workbook);

        workbook.SaveAs(filePath);
    }

    private static void WriteSchedulerSheet(XLWorkbook workbook)
    {
        var ws = workbook.Worksheets.Add("Scheduler");
        ws.Cell(1, 1).Value = "Key";
        ws.Cell(1, 2).Value = "Value";

        ws.Cell(2, 1).Value = "BlocksPerDay";
        ws.Cell(2, 2).Value = 9;

        ws.Cell(3, 1).Value = "RoomChangePenalty";
        ws.Cell(3, 2).Value = 3;

        ws.Cell(4, 1).Value = "SolverTimeLimitSeconds";
        ws.Cell(4, 2).Value = 10.0;

        ws.Columns().AdjustToContents();
    }

    private static void WriteDaysSheet(XLWorkbook workbook)
    {
        var ws = workbook.Worksheets.Add("Days");
        ws.Cell(1, 1).Value = "Day";

        ws.Cell(2, 1).Value = "Monday";
        ws.Cell(3, 1).Value = "Tuesday";
        ws.Cell(4, 1).Value = "Wednesday";
        ws.Cell(5, 1).Value = "Thursday";
        ws.Cell(6, 1).Value = "Friday";

        ws.Columns().AdjustToContents();
    }

    private static void WriteTeachersSheet(XLWorkbook workbook)
    {
        var ws = workbook.Worksheets.Add("Teachers");
        ws.Cell(1, 1).Value = "Id";
        ws.Cell(1, 2).Value = "FullName";
        ws.Cell(1, 3).Value = "PreferredRoom";
        ws.Cell(1, 4).Value = "TargetLoadBlocks";

        ws.Cell(2, 1).Value = "T001";
        ws.Cell(2, 2).Value = "Alice Smith";
        ws.Cell(2, 3).Value = "Room 101";
        ws.Cell(2, 4).Value = 10;

        ws.Columns().AdjustToContents();
    }

    private static void WriteClassesSheet(XLWorkbook workbook)
    {
        var ws = workbook.Worksheets.Add("Classes");
        ws.Cell(1, 1).Value = "Key";
        ws.Cell(1, 2).Value = "Department";
        ws.Cell(1, 3).Value = "Name";
        ws.Cell(1, 4).Value = "WeeklyBlocks";
        ws.Cell(1, 5).Value = "PreferredRoom";

        ws.Cell(2, 1).Value = "MATH101";
        ws.Cell(2, 2).Value = "MATH";
        ws.Cell(2, 3).Value = "Mathematics";
        ws.Cell(2, 4).Value = 4;
        ws.Cell(2, 5).Value = "Room 201";

        ws.Columns().AdjustToContents();
    }

    private static void WriteDepartmentsSheet(XLWorkbook workbook)
    {
        var ws = workbook.Worksheets.Add("Departments");
        ws.Cell(1, 1).Value = "Key";
        ws.Cell(1, 2).Value = "Name";

        ws.Cell(2, 1).Value = "MATH";
        ws.Cell(2, 2).Value = "Mathematics";

        ws.Columns().AdjustToContents();
    }

    private static void WriteTeacherDepartmentsSheet(XLWorkbook workbook)
    {
        var ws = workbook.Worksheets.Add("TeacherDepartments");
        ws.Cell(1, 1).Value = "TeacherId";
        ws.Cell(1, 2).Value = "Department";

        ws.Cell(2, 1).Value = "T001";
        ws.Cell(2, 2).Value = "MATH";

        ws.Columns().AdjustToContents();
    }
}