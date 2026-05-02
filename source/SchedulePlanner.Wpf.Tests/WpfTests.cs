using SchedulePlanner.Wpf.ViewModels;

namespace SchedulePlanner.Wpf.Tests
{
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
    }
}
