using System.Collections.Concurrent;
using System.Diagnostics;
using System.IO;
using System.IO.Abstractions;
using System.Text;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using Microsoft.Extensions.Options;
using SchedulePlanner.ImportExport.Excel;

namespace SchedulePlanner.Wpf.Helpers
{
    public sealed class FileLogger<T> : ILogger<T>, IDisposable, IAsyncDisposable
    {
        private readonly ILogger _logger;
        private readonly IFileSystem _fileSystem;
        private readonly string _filePath;
        private readonly string _categoryName;
        private readonly bool _appendToExisting = true;
        private readonly int _delay = 500;
        private CancellationTokenSource? _cts = null;
        private readonly ConcurrentQueue<string> _writeQueue = new();

        public FileLogger(IOptions<ImportExportOptions> options, ILogger? logger = null, IFileSystem? fileSystem = null)
        {
            _categoryName = typeof(T).Name;
            var fileName = $"scheduling-log_{DateTime.UtcNow.ToDateTimeName()}.txt";
            _filePath = Path.Combine(options.Value.Directory, fileName);
            _fileSystem = fileSystem ?? new FileSystem();
            _logger = logger ?? NullLogger.Instance;
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
            _logger.Log(logLevel, eventId, state, exception, formatter);

            if (!IsEnabled(logLevel))
                return;

            var line = formatter(state, exception);
            if (string.IsNullOrWhiteSpace(line) && exception is null)
                return;

            if (exception != null)
                line += $"{Environment.NewLine}{exception}";

            Enqueue(line);
        }

        public async Task<string> ReadAllTextAsync()
        {
            if (!_fileSystem.File.Exists(_filePath))
                return string.Empty;
            string? line;
            while (_writeQueue.TryDequeue(out line))
                await WriteLineAsync(line).ConfigureAwait(false);
            var textReadFromFile = new StringBuilder();
            using var streamReader = _fileSystem.File.OpenText(_filePath);
            while ((line = await streamReader.ReadLineAsync()) != null)
                textReadFromFile.AppendLine(line);
            return textReadFromFile.ToString();
        }

        private void Enqueue(string line)
        {
            if (_cts == null)
                Initialise();
            _writeQueue.Enqueue(line);
        }

        private void Initialise()
        {
            _cts = new CancellationTokenSource();
            Task.Run(InitialiseAsync);
        }

        private async Task InitialiseAsync()
        {
            var directoryName = _fileSystem.Path.GetDirectoryName(_filePath);
            if (!string.IsNullOrWhiteSpace(directoryName))
                _fileSystem.Directory.CreateDirectory(directoryName);
            await WriteLineAsync(_filePath + Environment.NewLine).ConfigureAwait(false);
            await TryWriteAllAsync().ConfigureAwait(false);
        }

        private async Task TryWriteAllAsync()
        {
            Debug.Assert(_cts != null, "CancellationTokenSource should have been initialised before writing.");
            while (!_cts.Token.IsCancellationRequested)
            {
                if (_writeQueue.TryDequeue(out var line))
                {
                    await WriteLineAsync(line).ConfigureAwait(false);
                }
                else if (_writeQueue.IsEmpty)
                {
                    await Task.Delay(_delay, _cts.Token).ConfigureAwait(false);
                }
            }
        }

        private async Task WriteLineAsync(string textToWrite)
        {
            using var streamWriter = _appendToExisting ?
                _fileSystem.File.AppendText(_filePath) :
                _fileSystem.File.CreateText(_filePath);
            await streamWriter.WriteLineAsync(textToWrite).ConfigureAwait(false);
        }

        public override string ToString() => _filePath;

        public async ValueTask DisposeAsync()
        {
            if (_cts == null)
                return;
            while (_writeQueue.TryDequeue(out var line))
                await WriteLineAsync(line).ConfigureAwait(false);
            Debug.Assert(_writeQueue.IsEmpty, "Write queue cancelled while text was still being written");
            _cts.Cancel(false);
            _writeQueue.Clear();
            if (_fileSystem.File.Exists(_filePath))
                _fileSystem.File.Delete(_filePath);
        }

        public void Dispose()
        {
            DisposeAsync().GetAwaiter().GetResult();
        }

        private sealed class NullScope : IDisposable
        {
            public static readonly NullScope Instance = new();
            public void Dispose() { }
        }
    }
}