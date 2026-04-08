using Google.OrTools.Sat;

namespace SchedulePlanner.Core.Tests
{
    public class OptimizationBuilderTests
    {
        [Test]
        public async Task AddRoomChangeOptimization_ValidContext_ReturnsPenalties()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday, DayOfWeek.Tuesday },
                BlocksPerDay = 3,
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math", WeeklyBlocks = 2, PreferredRoom = "Room101" },
                    new Class { Key = "Math102", Department = "Math", WeeklyBlocks = 2, PreferredRoom = "Room102" }
                },
                Teachers = new List<Teacher>
                {
                    new Teacher { Id = "T1", FullName = "Teacher 1" }
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
            var optimizationBuilder = new OptimizationBuilder();

            var penalties = optimizationBuilder.AddRoomChangeOptimization(
                context, variables, config, 3, CancellationToken.None);

            await Assert.That(penalties).IsNotNull();
            await Assert.That(penalties.Count).IsGreaterThan(0);
        }

        [Test]
        public async Task AddRoomChangeOptimization_SameRoom_NoPenalties()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday },
                BlocksPerDay = 3,
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math", WeeklyBlocks = 2 },
                    new Class { Key = "Math102", Department = "Math", WeeklyBlocks = 2 }
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
            var optimizationBuilder = new OptimizationBuilder();

            var penalties = optimizationBuilder.AddRoomChangeOptimization(
                context, variables, config, 3, CancellationToken.None);

            await Assert.That(penalties).IsNotNull();
            // All classes have the same room, so no penalties should be generated
            await Assert.That(penalties.Count).IsEqualTo(0);
        }

        [Test]
        public async Task AddScheduleSpreadOptimization_ValidContext_ReturnsPenalties()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday, DayOfWeek.Tuesday },
                BlocksPerDay = 4,
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math", WeeklyBlocks = 2 },
                    new Class { Key = "Math102", Department = "Math", WeeklyBlocks = 2 }
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
            var optimizationBuilder = new OptimizationBuilder();

            var penalties = optimizationBuilder.AddScheduleSpreadOptimization(
                context, variables, config, 2, CancellationToken.None);

            await Assert.That(penalties).IsNotNull();
            await Assert.That(penalties.Count).IsGreaterThan(0);
        }

        [Test]
        public async Task AddScheduleSpreadOptimization_SameClass_NoPenalties()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday },
                BlocksPerDay = 4,
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
            var optimizationBuilder = new OptimizationBuilder();

            var penalties = optimizationBuilder.AddScheduleSpreadOptimization(
                context, variables, config, 2, CancellationToken.None);

            await Assert.That(penalties).IsNotNull();
            // Only one class, so no penalties should be generated
            await Assert.That(penalties.Count).IsEqualTo(0);
        }

        [Test]
        public async Task AddWeekDistributionOptimization_ValidContext_ReturnsPenalties()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday, DayOfWeek.Tuesday },
                BlocksPerDay = 3,
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math", WeeklyBlocks = 2 },
                    new Class { Key = "Math102", Department = "Math", WeeklyBlocks = 2 }
                },
                Teachers = new List<Teacher>
                {
                    new Teacher { Id = "T1", FullName = "Teacher 1" }
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
            var optimizationBuilder = new OptimizationBuilder();

            var penalties = optimizationBuilder.AddWeekDistributionOptimization(
                context, variables, config, 1, CancellationToken.None);

            await Assert.That(penalties).IsNotNull();
            await Assert.That(penalties.Count).IsGreaterThan(0);
        }

        [Test]
        public async Task AddClassDayClusteringOptimization_ValidContext_ReturnsPenalties()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday, DayOfWeek.Tuesday },
                BlocksPerDay = 3,
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math", WeeklyBlocks = 2 },
                    new Class { Key = "Math102", Department = "Math", WeeklyBlocks = 2 }
                },
                Teachers = new List<Teacher>
                {
                    new Teacher { Id = "T1", FullName = "Teacher 1" }
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
            var optimizationBuilder = new OptimizationBuilder();

            var penalties = optimizationBuilder.AddClassDayClusteringOptimization(
                context, variables, config, 1, CancellationToken.None);

            await Assert.That(penalties).IsNotNull();
            await Assert.That(penalties.Count).IsGreaterThan(0);
        }

        [Test]
        public async Task AddClassBlockConsistencyOptimization_ValidContext_ReturnsPenalties()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday, DayOfWeek.Tuesday },
                BlocksPerDay = 3,
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math", WeeklyBlocks = 2 },
                    new Class { Key = "Math102", Department = "Math", WeeklyBlocks = 2 }
                },
                Teachers = new List<Teacher>
                {
                    new Teacher { Id = "T1", FullName = "Teacher 1" }
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
            var optimizationBuilder = new OptimizationBuilder();

            var penalties = optimizationBuilder.AddClassBlockConsistencyOptimization(
                context, variables, config, 1, CancellationToken.None);

            await Assert.That(penalties).IsNotNull();
            await Assert.That(penalties.Count).IsGreaterThan(0);
        }
    }
}
