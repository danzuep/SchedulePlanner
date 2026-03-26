using System.Globalization;
using System.Text;
using ClosedXML.Excel;
using CsvHelper;

namespace SchedulePlanner.ImportExport
{
    public enum ExportFileType
    {
        Csv = 0,
        Xlsx = 1,
    }

    public static class ExportHelperCsvExcel
    {
        private const string ExcelDateTimeFormat = "dd/MM/yyyy HH:mm:ss";

        private static Dictionary<ExportFileType, string> _suffix = new Dictionary<ExportFileType, string>()
        {
            { ExportFileType.Csv, ".csv" },
            { ExportFileType.Xlsx, ".xlsx" },
        };

        public static string ToDateTimeName(this DateTime dateTime) =>
            string.Format("{0:yyyyMMdd_HHmmss}", dateTime);

        public static bool TryGetFile(this ExportFileType fileType, ref string filePath)
        {
            if (_suffix.TryGetValue(fileType, out var suffix))
                filePath += suffix;

            var fileInfo = new FileInfo(filePath);
            if (fileInfo.Directory != null && !fileInfo.Directory.Exists)
                fileInfo.Directory.Create();

            return !fileInfo.IsFileLocked();
        }

        public static void WriteToFile<T>(this IEnumerable<T> data, string filePath, string fileName = "",
            ExportFileType fileType = ExportFileType.Xlsx, int[]? hideColumnIndex = null, int[]? dateColumnIndex = null)
        {
            string fullPath = Path.Combine(filePath, fileName);

            if (_suffix.TryGetValue(fileType, out var suffix))
                ValidateExtension(ref fullPath, suffix);

            if (fileType.Equals(ExportFileType.Xlsx))
            {
                using (var workbook = data.WriteToWorkbook(hideColumnIndex, dateColumnIndex))
                    workbook.SaveAs(fullPath);
            }
            else if (fileType.Equals(ExportFileType.Csv))
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
            if (_suffix.TryGetValue(ExportFileType.Xlsx, out var suffix))
                filePath = GetValidatedFileName(filePath, suffix);
            using (var workbook = data.WriteToWorkbook(hideColumnIndex))
                workbook.SaveAs(filePath);
            return filePath;
        }

        public static MemoryStream WriteToStream<T>(this IEnumerable<T> data, ref string fileName, params int[] hideColumnIndex)
        {
            var outputStream = new MemoryStream();
            if (string.IsNullOrEmpty(fileName))
                fileName = DateTime.Now.ToDateTimeName();
            if (_suffix.TryGetValue(ExportFileType.Xlsx, out var suffix))
                fileName = GetValidatedFileName(fileName, suffix);
            using (var workbook = data.WriteToWorkbook(hideColumnIndex))
                workbook.SaveAs(outputStream);
            outputStream.Position = 0;
            return outputStream;
        }

        public static XLWorkbook WriteToWorkbook<T>(this IEnumerable<T> data, int[]? hideColumnIndex = null, int[]? dateColumnIndex = null)
        {
            var workbook = new XLWorkbook();
            if (!data.IsNullOrEmpty())
            {
                workbook.Worksheets.Add(data.CreateDataTable())
                    .Columns().AdjustToContents();
                var ws = workbook.Worksheets.FirstOrDefault();
                if (ws is null)
                    return workbook;
                if (hideColumnIndex?.Length > 0)
                    foreach (var toHide in hideColumnIndex)
                        ws.Column(toHide).Hide();
                if (dateColumnIndex?.Length > 0)
                    foreach (var toDate in dateColumnIndex)
                        ws.Column(toDate).Style.DateFormat.Format = ExcelDateTimeFormat;
            }
            return workbook;
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