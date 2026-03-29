namespace SchedulePlanner.ImportExport.Csv;

using System.Globalization;
using System.Text;
using System.IO.Abstractions;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using SchedulePlanner.Core;

public sealed record CsvOptions
{
    public static readonly string SectionName = "Csv";

    public string DirectoryPath { get; init; } = "data";
    public string TeachersFile { get; init; } = "teachers.csv";
    public string ClassesFile { get; init; } = "classes.csv";
    public string DepartmentsFile { get; init; } = "departments.csv";
    public string TeacherDepartmentsFile { get; init; } = "department_assignments.csv";
    public char Delimiter { get; init; } = ',';
    public bool HasHeader { get; init; } = true;
}

public interface ICsvSchedulerConfigBuilder
{
    Task<SchedulerConfig> BuildAsync(CancellationToken cancellationToken = default);
}

public sealed class CsvSchedulerConfigBuilder : ICsvSchedulerConfigBuilder
{
    private readonly CsvOptions _options;
    private readonly ILogger<CsvSchedulerConfigBuilder> _logger;
    private readonly IFileSystem _fileSystem;

    public CsvSchedulerConfigBuilder(
        IOptions<CsvOptions> options,
        ILogger<CsvSchedulerConfigBuilder> logger,
        IFileSystem fileSystem)
    {
        _options = options?.Value ?? throw new ArgumentNullException(nameof(options));
        _logger = logger ?? throw new ArgumentNullException(nameof(logger));
        _fileSystem = fileSystem ?? new FileSystem();
    }

    public async Task<SchedulerConfig> BuildAsync(CancellationToken cancellationToken = default)
    {
        var teachers = await ReadTeachersAsync(cancellationToken).ConfigureAwait(false);
        var departments = await ReadDepartmentsAsync(cancellationToken).ConfigureAwait(false);
        var teacherDepartments = await ReadTeacherDepartmentsAsync(cancellationToken).ConfigureAwait(false);
        var classes = await ReadClassesAsync(cancellationToken).ConfigureAwait(false);

        var config = new SchedulerConfig
        {
            Teachers = teachers,
            Departments = departments,
            TeacherDepartments = teacherDepartments,
            Classes = classes
        };

        _logger.LogInformation("Loaded CSV scheduler configuration from {Directory}. Teachers: {TeacherCount}, Classes: {ClassCount}",
            _options.DirectoryPath, teachers.Count, classes.Count);

        return config;
    }

    private async Task<List<Teacher>> ReadTeachersAsync(CancellationToken cancellationToken)
    {
        var rows = await ReadCsvAsync(_options.TeachersFile, cancellationToken).ConfigureAwait(false);
        var list = new List<Teacher>(rows.Count);
        foreach (var row in rows)
        {
            if (row.Length < 1)
            {
                throw new InvalidOperationException("Teachers CSV must contain at least an ID column.");
            }

            list.Add(new Teacher
            {
                Id = row[0].ToString(CultureInfo.InvariantCulture),
                FullName = row[1],
                PreferredRoom = row.ElementAtOrDefault(2) ?? string.Empty,
                TargetLoadBlocks = row.Length > 3 && int.TryParse(row[3], out var target) ? target : 10
            });
        }

        return list;
    }

    private async Task<List<Class>> ReadClassesAsync(CancellationToken cancellationToken)
    {
        var rows = await ReadCsvAsync(_options.ClassesFile, cancellationToken).ConfigureAwait(false);
        var list = new List<Class>(rows.Count);
        foreach (var row in rows)
        {
            if (row.Length < 4)
            {
                throw new InvalidOperationException("Classes CSV must contain Key, Department, Name, and WeeklyBlocks columns.");
            }

            if (!int.TryParse(row[3], NumberStyles.Integer, CultureInfo.InvariantCulture, out var weeklyBlocks))
            {
                throw new InvalidOperationException($"Invalid weekly blocks value '{row[3]}' for class '{row[0]}'.");
            }

            list.Add(new Class
            {
                Key = row[0],
                Department = row[1],
                Name = row[2],
                PreferredRoom = row.ElementAtOrDefault(4) ?? string.Empty,
                WeeklyBlocks = weeklyBlocks
            });
        }

        return list;
    }

    private async Task<List<Department>> ReadDepartmentsAsync(CancellationToken cancellationToken)
    {
        var rows = await ReadCsvAsync(_options.DepartmentsFile, cancellationToken).ConfigureAwait(false);
        var list = new List<Department>(rows.Count);
        foreach (var row in rows)
        {
            if (row.Length < 2)
            {
                throw new InvalidOperationException("Departments CSV must contain Key and Name columns.");
            }

            list.Add(new Department
            {
                Key = row[0],
                Name = row[1]
            });
        }

        return list;
    }

    private async Task<List<TeacherDepartment>> ReadTeacherDepartmentsAsync(CancellationToken cancellationToken)
    {
        var rows = await ReadCsvAsync(_options.TeacherDepartmentsFile, cancellationToken).ConfigureAwait(false);
        var list = new List<TeacherDepartment>(rows.Count);
        foreach (var row in rows)
        {
            if (row.Length < 2)
            {
                throw new InvalidOperationException("TeacherDepartments CSV must contain TeacherId and Department columns.");
            }

            list.Add(new TeacherDepartment
            {
                TeacherId = row[0],
                Department = row[1]
            });
        }

        return list;
    }

    private async Task<List<string[]>> ReadCsvAsync(string fileName, CancellationToken cancellationToken)
    {
        var path = _fileSystem.Path.Combine(_options.DirectoryPath, fileName);

        if (!_fileSystem.File.Exists(path))
        {
            throw new FileNotFoundException($"CSV file '{path}' not found.");
        }

        var result = new List<string[]>();
        await using var stream = _fileSystem.File.Open(path, FileMode.Open, FileAccess.Read, FileShare.Read);
        using var reader = new StreamReader(stream, Encoding.UTF8);

        if (_options.HasHeader)
        {
            await reader.ReadLineAsync().ConfigureAwait(false);
        }

        while (true)
        {
            cancellationToken.ThrowIfCancellationRequested();

            var line = await reader.ReadLineAsync().ConfigureAwait(false);
            if (line is null)
            {
                // Reached end of stream
                break;
            }

            var columns = line.Split(_options.Delimiter).Select(col => col.Trim()).ToArray();
            if (columns.Length == 0 || columns.All(string.IsNullOrWhiteSpace))
            {
                continue;
            }

            result.Add(columns);
        }

        return result;
    }
}

public static class ServiceCollectionExtensions
{
    public static IServiceCollection AddCsvSchedulerSources(this IServiceCollection services, IConfiguration configuration)
    {
        if (services == null)
        {
            throw new ArgumentNullException(nameof(services));
        }
        if (configuration == null)
        {
            throw new ArgumentNullException(nameof(configuration));
        }

        services.Configure<CsvOptions>(configuration.GetSection(CsvOptions.SectionName));
        services.AddTransient<ICsvSchedulerConfigBuilder, CsvSchedulerConfigBuilder>();
        services.AddSingleton<IFileSystem, FileSystem>();
        return services;
    }
}