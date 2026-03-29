using System.IO;
using Microsoft.Extensions.Logging;
using SchedulePlanner.Core;
using SchedulePlanner.ImportExport.Excel;

namespace SchedulePlanner.Wpf.Services
{
    public sealed class FileLogger : ILogger<SchedulingService>
    {
        private readonly string _categoryName;
        private readonly string _filePath;
        private readonly object _lock = new();

        public FileLogger(ImportExportOptions options)
        {
            _categoryName = nameof(SchedulingService);
            var directory = options.Directory;
            Directory.CreateDirectory(directory);
            var fileName = $"scheduling-log_{DateTime.UtcNow.ToDateTimeName()}.txt";
            _filePath = Path.Combine(directory, fileName);
            File.AppendAllText(_filePath, _filePath + Environment.NewLine);
        }

        public IDisposable BeginScope<TState>(TState state) => NullScope.Instance;

        public bool IsEnabled(LogLevel logLevel) => logLevel != LogLevel.None;

        public void Log<TState>(
            LogLevel logLevel,
            EventId eventId,
            TState state,
            Exception? exception,
            Func<TState, Exception?, string> formatter)
        {
            if (!IsEnabled(logLevel))
                return;

            var message = formatter(state, exception);
            if (string.IsNullOrWhiteSpace(message) && exception is null)
                return;

            var line = $"{DateTimeOffset.Now:yyyy-MM-dd HH:mm:ss.fff zzz} " +
                       $"[{logLevel}] " +
                       $"[{_categoryName}] " +
                       $"{message}";

            if (exception != null)
                line += $"{Environment.NewLine}{exception}";

            lock (_lock)
            {
                File.AppendAllText(_filePath, line + Environment.NewLine);
            }
        }

        public string ReadLog() => File.Exists(_filePath) ? File.ReadAllText(_filePath) : string.Empty;

        private sealed class NullScope : IDisposable
        {
            public static readonly NullScope Instance = new();
            public void Dispose() { }
        }
    }
}