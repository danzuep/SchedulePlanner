namespace SchedulePlanner.Worker.Tests
{
    public class WorkerTests
    {
        [Test]
        public async Task Worker_AssemblyLoads()
        {
            var type = typeof(SchedulePlanner.Worker.Program);
            await Assert.That(type).IsNotNull();
        }

        [Test]
        public async Task Worker_Service_Exists()
        {
            var type = typeof(SchedulePlanner.Worker.Program.Worker);
            await Assert.That(type).IsNotNull();
        }
    }
}
