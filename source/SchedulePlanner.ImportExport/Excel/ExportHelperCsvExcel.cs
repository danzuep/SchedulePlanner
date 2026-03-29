using System.Globalization;
using System.Text;
using ClosedXML.Excel;
using CsvHelper;

namespace SchedulePlanner.ImportExport.Excel
{
    public static class ExportHelperCsvExcel
    {
        private const string ExcelDateTimeFormat = "dd/MM/yyyy HH:mm:ss";

        private static Dictionary<ImportExportFileType, string> _suffix = new Dictionary<ImportExportFileType, string>()
        {
            { ImportExportFileType.Csv, ".csv" },
            { ImportExportFileType.Xlsx, ".xlsx" },
        };

        public static string ToDateTimeName(this DateTime dateTime) =>
            string.Format("{0:yyyyMMdd_HHmmss}", dateTime);

        public static bool TryGetFile(this ImportExportFileType fileType, ref string filePath)
        {
            if (_suffix.TryGetValue(fileType, out var suffix))
                filePath += suffix;

            var fileInfo = new FileInfo(filePath);
            if (fileInfo.Directory != null && !fileInfo.Directory.Exists)
                fileInfo.Directory.Create();

            return !fileInfo.IsFileLocked();
        }

        public static void WriteToFile<T>(this IEnumerable<T> data, string filePath, string fileName = "",
            ImportExportFileType fileType = ImportExportFileType.Xlsx, int[]? hideColumnIndex = null, int[]? dateColumnIndex = null)
        {
            string fullPath = Path.Combine(filePath, fileName);

            if (_suffix.TryGetValue(fileType, out var suffix))
                ValidateExtension(ref fullPath, suffix);

            if (fileType.Equals(ImportExportFileType.Xlsx))
            {
                using (var workbook = data.CreateWorkbook(hideColumnIndex, dateColumnIndex))
                    workbook.SaveAs(fullPath);
            }
            else if (fileType.Equals(ImportExportFileType.Csv))
            {
                using (var writer = new StreamWriter(fullPath, false))
                using (var csv = new CsvWriter(writer, CultureInfo.InvariantCulture))
                    csv.WriteRecords(data);
            }
            else
                throw new NotImplementedException(fileType.GetName());
        }

        public static string WriteToExcel<T>(this IEnumerable<T> data, string filePath, string fileName = "", params int[] hideColumnIndex)
        {
            string fullPath = Path.Combine(filePath, fileName);
            return data.WriteToExcel(fullPath, hideColumnIndex);
        }

        public static string WriteToExcel<T>(this IEnumerable<T> data, string filePath, params int[] hideColumnIndex)
        {
            if (_suffix.TryGetValue(ImportExportFileType.Xlsx, out var suffix))
                filePath = GetValidatedFileName(filePath, suffix);
            using (var workbook = data.CreateWorkbook(hideColumnIndex))
                workbook.SaveAs(filePath);
            return filePath;
        }

        public static MemoryStream WriteToStream<T>(this IEnumerable<T> data, ref string fileName, params int[] hideColumnIndex)
        {
            var outputStream = new MemoryStream();
            if (string.IsNullOrEmpty(fileName))
                fileName = DateTime.Now.ToDateTimeName();
            if (_suffix.TryGetValue(ImportExportFileType.Xlsx, out var suffix))
                fileName = GetValidatedFileName(fileName, suffix);
            using (var workbook = data.CreateWorkbook(hideColumnIndex))
                workbook.SaveAs(outputStream);
            outputStream.Position = 0;
            return outputStream;
        }

        public static XLWorkbook CreateWorkbook<T>(
            this IEnumerable<T> data,
            int[]? hideColumnIndex = null,
            int[]? dateColumnIndex = null)
        {
            var workbook = new XLWorkbook();
            workbook.AddWorksheet(data, hideColumnIndex, dateColumnIndex);
            return workbook;
        }

        public static void AddWorksheet<T>(
            this XLWorkbook workbook,
            IEnumerable<T> data,
            int[]? hideColumnIndex = null,
            int[]? dateColumnIndex = null)
        {
            if (workbook == null || data.IsNullOrEmpty())
                return;
            var ws = workbook.AddWorksheet();
            ws.FirstCell().InsertTable(data);
            ws.Columns().AdjustToContents();
            if (hideColumnIndex?.Length > 0)
                foreach (var toHide in hideColumnIndex)
                    ws.Column(toHide).Hide();
            if (dateColumnIndex?.Length > 0)
                foreach (var toDate in dateColumnIndex)
                    ws.Column(toDate).Style.DateFormat.Format = ExcelDateTimeFormat;
        }

        public static void AddKeyValueTable(
            this IXLWorksheet ws,
            IEnumerable<KeyValuePair<string, XLCellValue>> rows,
            string header1 = "Key",
            string header2 = "Value")
        {
            var row = 1;
            ws.Cell(row, 1).Value = header1;
            ws.Cell(row, 2).Value = header2;

            foreach (var item in rows)
            {
                row++;
                ws.Cell(row, 1).Value = item.Key;
                ws.Cell(row, 2).Value = item.Value;
            }
        }

        public static void InsertWorksheetTable<T>(this IXLWorkbook wb, IEnumerable<T> data, string name)
        {
            var ws = wb.AddWorksheet();
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
                return true;
            }
        }

        public static string GetValidatedFileName(string filePath, string suffix)
        {
            string validFileName = filePath ?? "";
            if (!suffix?.StartsWith(".") ?? false)
                suffix = $".{suffix}";
            var extension = Path.GetExtension(filePath);
            if (string.IsNullOrWhiteSpace(extension) &&
                !string.IsNullOrWhiteSpace(suffix))
                validFileName = $"{filePath}{suffix}";
            return validFileName;
        }

        public static void ValidateExtension(ref string filePath, string suffix)
        {
            if (!suffix?.StartsWith(".") ?? false)
            {
                var sb = new StringBuilder(".");
                sb.Append(suffix);
                suffix = sb.ToString();
            }
            var extension = Path.GetExtension(filePath);
            if (string.IsNullOrWhiteSpace(extension) &&
                !string.IsNullOrWhiteSpace(suffix))
            {
                var sb = new StringBuilder(filePath);
                sb.Append(suffix);
                filePath = sb.ToString();
            }
        }
    }
}