namespace SchedulePlanner.Cli.Tests
{
    public class CliTests
    {
        [Test]
        public async Task Cli_AssemblyLoads()
        {
            var type = typeof(Program);
            await Assert.That(type).IsNotNull();
        }

        [Explicit("Maually run the demo schedule to check it works without exceptions.")]
        [Category("Manual")]
        [Category("Integration")]
        [Test]
        public async Task RunDemoScheduleAsync()
        {
            await Program.RunDemoScheduleAsync();
        }
    }
}
