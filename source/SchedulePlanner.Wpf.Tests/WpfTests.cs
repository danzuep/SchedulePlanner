using Microsoft.Extensions.DependencyInjection;
using SchedulePlanner.Wpf.ViewModels;
using SchedulePlanner.Wpf.Services;
using SchedulePlanner.Wpf.Helpers;
using TUnit.Assertions;
using TUnit.Assertions.Extensions;
using TUnit.Core;

namespace SchedulePlanner.Wpf.Tests;

public class WpfTests
{
    [Test]
    public async Task Wpf_AssemblyLoads()
    {
        var type = typeof(MainViewModel);
        await Assert.That(type).IsNotNull();
    }

    [Test]
    public async Task Wpf_MainWindow_Exists()
    {
        var type = typeof(MainWindow);
        await Assert.That(type).IsNotNull();
    }

    [Test]
    public async Task Wpf_MainViewModel_InitialState_IsValid()
    {
        var dialogService = new TestDialogService();
        var vm = new MainViewModel(
            dialogService,
            new DummyServiceScopeFactory());

        await Assert.That(vm.StatusMessage).IsEqualTo("Ready.");
        await Assert.That(vm.IsBusy).IsFalse();
        await Assert.That(vm.TemporalStatus).IsEqualTo("Idle");
        await Assert.That(vm.Options).IsNotNull();
        await Assert.That(vm.ScheduleResult).IsNull();
        await Assert.That(vm.JobProgress).IsEqualTo(0);
    }

    [Test]
    public async Task Wpf_DialogService_Implementation_Works()
    {
        var dialog = new TestDialogService();
        await Assert.That(dialog.SaveFile()).IsNull();
        await Assert.That(dialog.OpenFile()).IsNull();
        dialog.ShowMessage("Test", "Message");
        dialog.ShowError("Test", "Error");
    }

        [Test]
        public async Task Wpf_IsZeroConverter_ConvertsCorrectly()
        {
            var converter = new IsZeroConverter();

            await Assert.That((bool)converter.Convert(0, typeof(bool), null, null)).IsTrue();
            await Assert.That((bool)converter.Convert(0.0, typeof(bool), null, null)).IsTrue();
            await Assert.That((bool)converter.Convert(1, typeof(bool), null, null)).IsFalse();
            await Assert.That((bool)converter.Convert(1.5, typeof(bool), null, null)).IsFalse();
            await Assert.That((bool)converter.Convert(null, typeof(bool), null, null)).IsTrue();
        }

        [Test]
        public async Task Wpf_MainViewModel_RunSolveCommand_StartsAndCompletes()
        {
            var dialogService = new TestDialogService();
            var vm = new MainViewModel(
                dialogService,
                new DummyServiceScopeFactory());

            await Assert.That(vm.IsBusy).IsFalse();
            await Assert.That(vm.JobProgress).IsEqualTo(0);
            await Assert.That(vm.ScheduleResult).IsNull();

            await vm.RunSolveAsync();

            await Assert.That(vm.IsBusy).IsFalse();
            await Assert.That(vm.JobProgress).IsEqualTo(100);
            await Assert.That(vm.ScheduleResult).IsNotNull();
            await Assert.That(vm.StatusMessage).IsEqualTo("Success: Optimal schedule found.");
            await Assert.That(vm.TemporalStatus).IsEqualTo("Idle");
        }

        [Test]
        public async Task Wpf_MainViewModel_RunSolveCommand_PopulatesResults()
        {
            var dialogService = new TestDialogService();
            var vm = new MainViewModel(
                dialogService,
                new DummyServiceScopeFactory());

            await vm.RunSolveAsync();

            await Assert.That(vm.ScheduleResult).IsNotNull();
            await Assert.That(vm.ScheduleResult.HasSolution).IsTrue();

            // Note: Actual assertions depend on the test data, but for now, just check it's not null
        }

        [Test]
        public async Task Wpf_MainViewModel_ExportSettingsCommand_ExecutesWithoutError()
        {
            var dialogService = new TestDialogService();
            var vm = new MainViewModel(
                dialogService,
                new DummyServiceScopeFactory());

            await Assert.That(vm.StatusMessage).IsEqualTo("Ready.");
            
            await vm.ExportSettingsAsync();

            await Assert.That(vm.IsBusy).IsFalse();
            await Assert.That(vm.StatusMessage).IsEqualTo("Ready.");
            await Assert.That(dialogService.LastSaveFileCalled).IsTrue();
        }

        [Test]
        public async Task Wpf_MainViewModel_ExportResultsCommand_ExecutesWithoutError()
        {
            var dialogService = new TestDialogService();
            var vm = new MainViewModel(
                dialogService,
                new DummyServiceScopeFactory());

            await Assert.That(vm.StatusMessage).IsEqualTo("Ready.");
            
            await vm.ExportResultsAsync();

            await Assert.That(vm.IsBusy).IsFalse();
            await Assert.That(vm.StatusMessage).IsEqualTo("Ready.");
            await Assert.That(dialogService.LastSaveFileCalled).IsTrue();
        }

        private class TestDialogService : IDialogService
        {
            public bool LastSaveFileCalled { get; private set; }
            public bool LastOpenFileCalled { get; private set; }

            public string? OpenFile()
            {
                LastOpenFileCalled = true;
                return null;
            }

            public string? SaveFile(string? defaultPath = null)
            {
                LastSaveFileCalled = true;
                return null;
            }

            public void ShowMessage(string title, string message) { }

            public void ShowError(string title, string message) { }
        }

        private class DummyServiceScopeFactory : IServiceScopeFactory
        {
            public IServiceScope CreateScope() => new DummyServiceScope();
        }

        private class DummyServiceScope : IServiceScope
        {
            public IServiceProvider ServiceProvider => new DummyServiceProvider();
            public void Dispose() { }
        }

        private class DummyServiceProvider : IServiceProvider
        {
            public object? GetService(Type serviceType)
            {
                if (serviceType == typeof(Microsoft.Extensions.Options.IOptions<SchedulePlanner.Core.SchedulerOptions>))
                {
                    return new DummyOptions();
                }
                if (serviceType == typeof(SchedulePlanner.Core.SchedulingService))
                {
                    return new DummySchedulingService();
                }
                if (serviceType == typeof(SchedulePlanner.ImportExport.ExportService))
                {
                    return new DummyExportService();
                }
                if (serviceType == typeof(SchedulePlanner.Cli.DemoScheduleRunner))
                {
                    return new DummyDemoScheduleRunner();
                }
                return null;
            }
        }

        private class DummyOptions : Microsoft.Extensions.Options.IOptions<SchedulePlanner.Core.SchedulerOptions>
        {
            public SchedulePlanner.Core.SchedulerOptions Value => new();
        }

        private class DummySchedulingService : SchedulePlanner.Core.SchedulingService
        {
            public DummySchedulingService() : base(new SchedulePlanner.Core.SchedulerOptions()) { }

            public override async Task<SchedulePlanner.Core.ScheduleResult> RunAsync(System.Threading.CancellationToken cancellationToken = default, IProgress<SchedulePlanner.Core.SolverProgress>? progress = null, TimeSpan? progressTimeout = null)
            {
                progress?.Report(new SchedulePlanner.Core.SolverProgress("Starting", null, null, null, 0, DateTime.UtcNow));
                await Task.Delay(1); // Dummy delay
                progress?.Report(new SchedulePlanner.Core.SolverProgress("Complete", 100, 100, 100, 1, DateTime.UtcNow));
                return new SchedulePlanner.Core.ScheduleResult("Test solution", true, 100, [], [], [], [], null, null, null);
            }
        }

        private class DummyExportService
        {
            public Task<string> ExportTemplateAsync(SchedulePlanner.Core.SchedulerOptions options, string path, bool addTimestamp = false)
            {
                return Task.FromResult("dummy path");
            }

            public Task<string> ExportToExcelAsync(SchedulePlanner.ImportExport.ScheduleResultExportOptions options)
            {
                return Task.FromResult("dummy path");
            }
        }

        private class DummyDemoScheduleRunner : SchedulePlanner.Cli.DemoScheduleRunner
        {
            public DummyDemoScheduleRunner() : base(null!, null!) { }

            public override async Task<SchedulePlanner.Core.ScheduleResult> RunAsync(System.Threading.CancellationToken cancellationToken = default, IProgress<SchedulePlanner.Core.SolverProgress>? progress = null, TimeSpan? progressTimeout = null)
            {
                await Task.Delay(1); // Dummy delay
                return new SchedulePlanner.Core.ScheduleResult("Demo solution", true, null, [], [], [], [], null, null, null);
            }
        }
    }
