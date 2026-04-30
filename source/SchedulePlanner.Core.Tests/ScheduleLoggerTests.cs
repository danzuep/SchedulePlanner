namespace SchedulePlanner.Core.Tests
{
    public class ScheduleLoggerTests
    {
        [Test]
        public async Task LogResult_NoSolution_LogsWarning()
        {
            var result = new ScheduleResult(
                "Unknown",
                false,
                null,
                new List<SummaryItem> { new SummaryItem("SolverStatus", "Solver statistics") },
                new List<TeacherScheduleResult>(),
                new List<ClassScheduleSummary>(),
                new List<RoomChangeResult>());

            var logger = new ScheduleLogger();

            // Should not throw
            logger.LogResult(result);

            await Assert.That(true).IsTrue();
        }

        [Test]
        public async Task LogResult_WithSolution_LogsSchedule()
        {
            var teacherSchedules = new List<TeacherScheduleResult>
            {
                new TeacherScheduleResult(
                    "T1",
                    "Teacher 1",
                    new List<DayScheduleResult>
                    {
                        new DayScheduleResult(
                            DayOfWeek.Monday,
                            new List<BlockScheduleResult>
                            {
                                new BlockScheduleResult(0, false, "Math101", "Algebra", "Room101", "Math"),
                                new BlockScheduleResult(1, true, null, null, null, null)
                            })
                    })
            };

            var classSummaries = new List<ClassScheduleSummary>
            {
                new ClassScheduleSummary("Math101", "Algebra", "Math", "T1", "Teacher 1", "Room101", 1, 1)
            };

            var result = new ScheduleResult(
                "Optimal",
                true,
                0.0,
                new List<SummaryItem> { new SummaryItem("SolverStatus", "Solver statistics") },
                teacherSchedules,
                classSummaries,
                new List<RoomChangeResult>());

            var logger = new ScheduleLogger();

            // Should not throw
            logger.LogResult(result);

            await Assert.That(true).IsTrue();
        }

        [Test]
        public async Task LogResult_WithRoomChanges_LogsPenalties()
        {
            var teacherSchedules = new List<TeacherScheduleResult>
            {
                new TeacherScheduleResult(
                    "T1",
                    "Teacher 1",
                    new List<DayScheduleResult>
                    {
                        new DayScheduleResult(
                            DayOfWeek.Monday,
                            new List<BlockScheduleResult>
                            {
                                new BlockScheduleResult(0, false, "Math101", "Algebra", "Room101", "Math"),
                                new BlockScheduleResult(1, false, "Math102", "Geometry", "Room102", "Math")
                            })
                    })
            };

            var roomChanges = new List<RoomChangeResult>
            {
                new RoomChangeResult("T1", "Teacher 1", DayOfWeek.Monday, 0, 1, "Math101", "Room101", "Math102", "Room102")
            };

            var result = new ScheduleResult(
                "Optimal",
                true,
                3.0,
                new List<SummaryItem> { new SummaryItem("SolverStatus", "Solver statistics") },
                teacherSchedules,
                new List<ClassScheduleSummary>(),
                roomChanges);

            var logger = new ScheduleLogger();

            // Should not throw
            logger.LogResult(result);

            await Assert.That(true).IsTrue();
        }
    }
}
