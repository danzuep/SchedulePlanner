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

        [Test]
        public async Task RunAsync_WithBasicScenario_Succeeds()
        {
            var options = SyntheticDataFactory.GenerateBasicScenario();
            var service = new SchedulingService(options);

            var result = await service.RunAsync();

            await Assert.That(result.HasSolution).IsTrue();
            await Assert.That(result.TeacherSchedules.Count).IsEqualTo(3);
        }

        [Test]
        public async Task RunAsync_WithStreamedScenario_Succeeds()
        {
            var options = SyntheticDataFactory.GenerateStreamedScenario();
            var service = new SchedulingService(options);

            var result = await service.RunAsync();

            await Assert.That(result.HasSolution).IsTrue();
            await Assert.That(result.StreamSchedules).IsNotEmpty();
        }

        [Test]
        public async Task RunAsync_WithBlockPeriodScenario_Succeeds()
        {
            var options = SyntheticDataFactory.GenerateBlockPeriodScenario();
            var service = new SchedulingService(options);

            var result = await service.RunAsync();

            await Assert.That(result.HasSolution).IsTrue();
        }

        [Test]
        public async Task RunAsync_WithSharedClassroomScenario_Succeeds()
        {
            var options = SyntheticDataFactory.GenerateSharedClassroomScenario();
            var service = new SchedulingService(options);

            var result = await service.RunAsync();

            await Assert.That(result.HasSolution).IsTrue();
        }

        [Test]
        public async Task RunAsync_WithCombinedScenario_Succeeds()
        {
            var options = SyntheticDataFactory.GenerateCombinedScenario();
            var service = new SchedulingService(options);

            var result = await service.RunAsync();

            await Assert.That(result.HasSolution).IsTrue();
        }

        [Test]
        public async Task RunAsync_WithLargeK12School_Succeeds()
        {
            var options = SyntheticDataFactory.GenerateLargeK12School();
            var service = new SchedulingService(options);

            var result = await service.RunAsync();

            await Assert.That(result.HasSolution).IsTrue();
            await Assert.That(result.TeacherSchedules.Count).IsGreaterThan(50);
            await Assert.That(result.Classes.Count).IsGreaterThan(50);
        }

        [Test]
        public async Task RunAsync_WithSyntheticDataBuilder_Succeeds()
        {
            var builder = new SyntheticDataBuilder { SchoolSize = 200, StreamCountPerClass = 3, BlockComplexity = 2 };
            var options = builder.Build();
            var service = new SchedulingService(options);

            var result = await service.RunAsync();

            await Assert.That(result.HasSolution).IsTrue();
        }

        [Test]
        public async Task PerformanceBenchmark_BasicScenario()
        {
            var options = SyntheticDataFactory.GenerateBasicScenario();
            var service = new SchedulingService(options);

            var stopwatch = System.Diagnostics.Stopwatch.StartNew();
            var result = await service.RunAsync();
            stopwatch.Stop();

            await Assert.That(result.HasSolution).IsTrue();
            Console.WriteLine($"Basic scenario solved in {stopwatch.ElapsedMilliseconds} ms");
        }

        [Test]
        public async Task PerformanceBenchmark_LargeK12School()
        {
            var options = SyntheticDataFactory.GenerateLargeK12School();
            var service = new SchedulingService(options);

            var stopwatch = System.Diagnostics.Stopwatch.StartNew();
            var result = await service.RunAsync();
            stopwatch.Stop();

            await Assert.That(result.HasSolution).IsTrue();
            Console.WriteLine($"Large K12 school solved in {stopwatch.ElapsedMilliseconds} ms");
        }
    }
}
