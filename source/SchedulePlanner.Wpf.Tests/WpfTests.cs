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
            await Assert.That(vm.IsSolving).IsFalse();
            await Assert.That(vm.TemporalStatus).IsEqualTo("Idle");
            await Assert.That(vm.Settings).IsNotNull();
            await Assert.That(vm.Results).IsNotNull();
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
        await Assert.That(true).IsTrue();
    }

        [Test]
        public async Task Wpf_IsZeroConverter_ConvertsCorrectly()
        {
            var converter = new IsZeroConverter();
            
            await Assert.That(converter.Convert(0, typeof(bool), null, null)).IsEqualTo(true);
            await Assert.That(converter.Convert(0.0, typeof(bool), null, null)).IsEqualTo(true);
            await Assert.That(converter.Convert(1, typeof(bool), null, null)).IsEqualTo(false);
            await Assert.That(converter.Convert(1.5, typeof(bool), null, null)).IsEqualTo(false);
            await Assert.That(converter.Convert(null, typeof(bool), null, null)).IsEqualTo(true);
        }

        [Test]
        public async Task Wpf_MainViewModel_RunSolveCommand_StartsAndCompletes()
        {
            var dialogService = new TestDialogService();
            var vm = new MainViewModel(
                dialogService,
                new DummyServiceScopeFactory());

            await Assert.That(vm.IsBusy).IsFalse();
            await Assert.That(vm.IsSolving).IsFalse();
            await Assert.That(vm.JobProgress).IsEqualTo(0);
            await Assert.That(vm.Results.Count).IsEqualTo(0);

            await vm.RunSolveAsync();

            await Assert.That(vm.IsBusy).IsFalse();
            await Assert.That(vm.IsSolving).IsFalse();
            await Assert.That(vm.JobProgress).IsEqualTo(100);
            await Assert.That(vm.Results.Count).IsEqualTo(2);
            await Assert.That(vm.StatusMessage).IsEqualTo("Solve complete. View results in the Results tab.");
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

            await Assert.That(vm.Results.Count).IsEqualTo(2);
            
            var first = vm.Results[0];
            await Assert.That(first.Teacher).IsEqualTo("Smith");
            await Assert.That(first.Class).IsEqualTo("Math 101");
            await Assert.That(first.Room).IsEqualTo("Lab 1");
            await Assert.That(first.Day).IsEqualTo("Monday");
            await Assert.That(first.Block).IsEqualTo(1);

            var second = vm.Results[1];
            await Assert.That(second.Teacher).IsEqualTo("Jones");
            await Assert.That(second.Class).IsEqualTo("History 2");
            await Assert.That(second.Room).IsEqualTo("Room 202");
            await Assert.That(second.Day).IsEqualTo("Monday");
            await Assert.That(second.Block).IsEqualTo(2);
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
            public object? GetService(Type serviceType) => null;
        }
    }
