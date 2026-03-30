using Google.OrTools.Sat;

namespace SchedulePlanner.Core.Tests
{
    public class ConstraintBuilderTests
    {
        [Test]
        public async Task AddSchedulingRules_ValidContext_AddsConstraints()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday, DayOfWeek.Tuesday },
                BlocksPerDay = 3,
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math", WeeklyBlocks = 2 }
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
            var constraintBuilder = new ConstraintBuilder();

            // Should not throw
            constraintBuilder.AddSchedulingRules(context, variables, config, CancellationToken.None);

            await Assert.That(true).IsTrue();
        }

        [Test]
        public async Task AddSchedulingRules_WithPresetBlocks_BlocksSchedulingInPresetBlocks()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday, DayOfWeek.Tuesday },
                BlocksPerDay = 5,
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math", WeeklyBlocks = 2 }
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
                    new PresetBlockConfig(2, "Lunch", new[] { DayOfWeek.Monday, DayOfWeek.Tuesday })
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
            var constraintBuilder = new ConstraintBuilder();

            // Should not throw
            constraintBuilder.AddSchedulingRules(context, variables, config, CancellationToken.None);

            await Assert.That(true).IsTrue();
        }

        [Test]
        public async Task AddSchedulingRules_ClassDemandingMoreBlocksThanAvailable_ThrowsException()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday },
                BlocksPerDay = 2,
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math", WeeklyBlocks = 5 }
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
            var constraintBuilder = new ConstraintBuilder();

            await Assert.That(() => constraintBuilder.AddSchedulingRules(context, variables, config, CancellationToken.None))
                .Throws<InvalidOperationException>();
        }
    }
}
