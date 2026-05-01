namespace SchedulePlanner.Core.Tests
{
    public class CliTests
    {
        [Test]
        public async Task Cli_AssemblyLoads()
        {
            var type = typeof(SchedulePlanner.Cli.Program);
            await Assert.That(type).IsNotNull();
        }
    }
}
