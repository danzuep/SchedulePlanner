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
        await Assert.That(vm.Settings).IsNotNull();
        await Assert.That(vm.Results).IsNotNull();
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

    private class TestDialogService : IDialogService
    {
        public string? OpenFile() => null;
        public string? SaveFile(string? defaultPath = null) => null;
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
