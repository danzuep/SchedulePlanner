using Google.OrTools.Sat;

namespace SchedulePlanner.Core.Tests
{
    public class ResultBuilderTests
    {
        [Test]
        public async Task BuildResult_NoSolution_ReturnsEmptyResult()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday },
                BlocksPerDay = 2,
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math", WeeklyBlocks = 1 }
                },
                Teachers = new List<Teacher>
                {
                    new Teacher { Id = "T1", FullName = "Teacher 1", PreferredRoom = "Room101" }
                },
                TeacherDepartments = new List<TeacherDepartment>
                {
                    new TeacherDepartment { TeacherId = "T1", Department = "Math" }
                }
            };

            var classAssignmentBuilder = new ClassAssignmentBuilder();
            var classAssignments = classAssignmentBuilder.BuildClassAssignments(config);
            var teacherGroups = classAssignmentBuilder.BuildTeacherGroups(classAssignments);
            var roomGroups = classAssignmentBuilder.BuildRoomGroups(classAssignments);

            var context = new SchedulingContext(
                new CpModel(),
                classAssignments,
                teacherGroups,
                roomGroups,
                config.Days.Count,
                config.BlocksPerDay);

            var assignment = new BoolVar[classAssignments.Count, config.Days.Count, config.BlocksPerDay];
            for (var cls = 0; cls < classAssignments.Count; ++cls)
            {
                for (var day = 0; day < config.Days.Count; ++day)
                {
                    for (var block = 0; block < config.BlocksPerDay; ++block)
                    {
                        assignment[cls, day, block] = context.Model.NewBoolVar(
                            $"assign_{classAssignments[cls].Config.Key}_day{day}_block{block}");
                    }
                }
            }

            var variables = new ScheduleVariables(assignment);
            var solver = new CpSolver();
            var resultBuilder = new ResultBuilder();

            var result = resultBuilder.BuildResult(
                context, variables, new List<RoomChangePenalty>(), config, solver, CpSolverStatus.Unknown, TimeSpan.Zero);

            await Assert.That(result).IsNotNull();
            await Assert.That(result.HasSolution).IsFalse();
            await Assert.That(result.TeacherSchedules.Count).IsEqualTo(0);
            await Assert.That(result.Classes.Count).IsEqualTo(0);
            await Assert.That(result.RoomChanges.Count).IsEqualTo(0);
        }

        [Test]
        public async Task BuildResult_WithSolution_ReturnsResult()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday },
                BlocksPerDay = 2,
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math", WeeklyBlocks = 1 }
                },
                Teachers = new List<Teacher>
                {
                    new Teacher { Id = "T1", FullName = "Teacher 1", PreferredRoom = "Room101" }
                },
                TeacherDepartments = new List<TeacherDepartment>
                {
                    new TeacherDepartment { TeacherId = "T1", Department = "Math" }
                }
            };

            var classAssignmentBuilder = new ClassAssignmentBuilder();
            var classAssignments = classAssignmentBuilder.BuildClassAssignments(config);
            var teacherGroups = classAssignmentBuilder.BuildTeacherGroups(classAssignments);
            var roomGroups = classAssignmentBuilder.BuildRoomGroups(classAssignments);

            var context = new SchedulingContext(
                new CpModel(),
                classAssignments,
                teacherGroups,
                roomGroups,
                config.Days.Count,
                config.BlocksPerDay);

            var assignment = new BoolVar[classAssignments.Count, config.Days.Count, config.BlocksPerDay];
            for (var cls = 0; cls < classAssignments.Count; ++cls)
            {
                for (var day = 0; day < config.Days.Count; ++day)
                {
                    for (var block = 0; block < config.BlocksPerDay; ++block)
                    {
                        assignment[cls, day, block] = context.Model.NewBoolVar(
                            $"assign_{classAssignments[cls].Config.Key}_day{day}_block{block}");
                    }
                }
            }

            var variables = new ScheduleVariables(assignment);
            var solver = new CpSolver();
            var status = solver.Solve(context.Model);
            var resultBuilder = new ResultBuilder();

            var result = resultBuilder.BuildResult(
                context, variables, new List<RoomChangePenalty>(), config, solver, status, TimeSpan.Zero);

            await Assert.That(result).IsNotNull();
            await Assert.That(result.HasSolution).IsTrue();
            await Assert.That(result.TeacherSchedules.Count).IsEqualTo(1);
            await Assert.That(result.Classes.Count).IsEqualTo(1);
            await Assert.That(result.TeacherSchedules[0].TeacherId).IsEqualTo("T1");
            await Assert.That(result.Classes[0].ClassKey).IsEqualTo("Math101");
        }

        [Test]
        public async Task BuildResult_WithPresetBlocks_IncludesPresetBlocks()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday },
                BlocksPerDay = 3,
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math", WeeklyBlocks = 1 }
                },
                Teachers = new List<Teacher>
                {
                    new Teacher { Id = "T1", FullName = "Teacher 1", PreferredRoom = "Room101" }
                },
                TeacherDepartments = new List<TeacherDepartment>
                {
                    new TeacherDepartment { TeacherId = "T1", Department = "Math" }
                },
                PresetBlocks = new List<PresetBlockConfig>
                {
                    new PresetBlockConfig(1, "Lunch", new[] { DayOfWeek.Monday })
                }
            };

            var classAssignmentBuilder = new ClassAssignmentBuilder();
            var classAssignments = classAssignmentBuilder.BuildClassAssignments(config);
            var teacherGroups = classAssignmentBuilder.BuildTeacherGroups(classAssignments);
            var roomGroups = classAssignmentBuilder.BuildRoomGroups(classAssignments);

            var context = new SchedulingContext(
                new CpModel(),
                classAssignments,
                teacherGroups,
                roomGroups,
                config.Days.Count,
                config.BlocksPerDay);

            var assignment = new BoolVar[classAssignments.Count, config.Days.Count, config.BlocksPerDay];
            for (var cls = 0; cls < classAssignments.Count; ++cls)
            {
                for (var day = 0; day < config.Days.Count; ++day)
                {
                    for (var block = 0; block < config.BlocksPerDay; ++block)
                    {
                        assignment[cls, day, block] = context.Model.NewBoolVar(
                            $"assign_{classAssignments[cls].Config.Key}_day{day}_block{block}");
                    }
                }
            }

            var variables = new ScheduleVariables(assignment);
            var solver = new CpSolver();
            var status = solver.Solve(context.Model);
            var resultBuilder = new ResultBuilder();

            var result = resultBuilder.BuildResult(
                context, variables, new List<RoomChangePenalty>(), config, solver, status, TimeSpan.Zero);

            await Assert.That(result).IsNotNull();
            await Assert.That(result.HasSolution).IsTrue();
            await Assert.That(result.TeacherSchedules[0].Days[0].Blocks.Count).IsEqualTo(3);
            await Assert.That(result.TeacherSchedules[0].Days[0].Blocks[1].ClassKey).IsEqualTo("Lunch");
            await Assert.That(result.TeacherSchedules[0].Days[0].Blocks[1].IsFree).IsFalse();
        }
    }
}
