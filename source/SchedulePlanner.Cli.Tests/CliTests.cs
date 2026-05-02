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
    }
}
