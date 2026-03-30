namespace SchedulePlanner.Core.Tests
{
    public class BasicTests
    {
        [Test]
        public async Task RunAsync_Returns()
        {
            var options = new SchedulerOptions();
            var service = new SchedulingService(options);

            var action = async () => await service.RunAsync();

            await Assert.That(action).ThrowsException()
                .WithMessage("At least one class must be defined.");
        }
    }
}
