namespace SchedulePlanner.Core.Tests
{
    public class ConfigValidatorTests
    {
        [Test]
        public async Task ValidateAndNormalizeConfig_ValidConfig_ReturnsNormalizedSettings()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday, DayOfWeek.Tuesday },
                BlocksPerDay = 5,
                Classes = new List<Class> { new Class { Key = "Math101", Department = "Math" } },
                Teachers = new List<Teacher> { new Teacher { Id = "T1", FullName = "Teacher 1" } },
                TeacherDepartments = new List<TeacherDepartment> { new TeacherDepartment { TeacherId = "T1", Department = "Math" } },
                SolverTimeLimitSeconds = 15.0,
                RoomChangePenalty = 5,
                ScheduleSpreadPenalty = 3
            };

            var validator = new ConfigValidator();
            var result = validator.ValidateAndNormalizeConfig(config);

            await Assert.That(result).IsNotNull();
            await Assert.That(result.SolverTimeLimitSeconds).IsEqualTo(15.0);
            await Assert.That(result.RoomChangePenalty).IsEqualTo(5);
            await Assert.That(result.ScheduleSpreadPenalty).IsEqualTo(3);
        }

        [Test]
        public async Task ValidateAndNormalizeConfig_NoDays_ThrowsException()
        {
            var config = new SchedulerOptions
            {
                Days = Array.Empty<DayOfWeek>(),
                BlocksPerDay = 5,
                Classes = new List<Class> { new Class { Key = "Math101", Department = "Math" } },
                Teachers = new List<Teacher> { new Teacher { Id = "T1", FullName = "Teacher 1" } },
                TeacherDepartments = new List<TeacherDepartment> { new TeacherDepartment { TeacherId = "T1", Department = "Math" } }
            };

            var validator = new ConfigValidator();

            await Assert.That(() => validator.ValidateAndNormalizeConfig(config))
                .Throws<InvalidOperationException>();
        }

        [Test]
        public async Task ValidateAndNormalizeConfig_ZeroBlocksPerDay_ThrowsException()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday },
                BlocksPerDay = 0,
                Classes = new List<Class> { new Class { Key = "Math101", Department = "Math" } },
                Teachers = new List<Teacher> { new Teacher { Id = "T1", FullName = "Teacher 1" } },
                TeacherDepartments = new List<TeacherDepartment> { new TeacherDepartment { TeacherId = "T1", Department = "Math" } }
            };

            var validator = new ConfigValidator();

            await Assert.That(() => validator.ValidateAndNormalizeConfig(config))
                .Throws<InvalidOperationException>();
        }

        [Test]
        public async Task ValidateAndNormalizeConfig_NoClasses_ThrowsException()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday },
                BlocksPerDay = 5,
                Classes = new List<Class>(),
                Teachers = new List<Teacher> { new Teacher { Id = "T1", FullName = "Teacher 1" } },
                TeacherDepartments = new List<TeacherDepartment> { new TeacherDepartment { TeacherId = "T1", Department = "Math" } }
            };

            var validator = new ConfigValidator();

            await Assert.That(() => validator.ValidateAndNormalizeConfig(config))
                .Throws<InvalidOperationException>();
        }

        [Test]
        public async Task ValidateAndNormalizeConfig_NoTeachers_ThrowsException()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday },
                BlocksPerDay = 5,
                Classes = new List<Class> { new Class { Key = "Math101", Department = "Math" } },
                Teachers = new List<Teacher>(),
                TeacherDepartments = new List<TeacherDepartment> { new TeacherDepartment { TeacherId = "T1", Department = "Math" } }
            };

            var validator = new ConfigValidator();

            await Assert.That(() => validator.ValidateAndNormalizeConfig(config))
                .Throws<InvalidOperationException>();
        }

        [Test]
        public async Task ValidateAndNormalizeConfig_NoTeacherDepartments_ThrowsException()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday },
                BlocksPerDay = 5,
                Classes = new List<Class> { new Class { Key = "Math101", Department = "Math" } },
                Teachers = new List<Teacher> { new Teacher { Id = "T1", FullName = "Teacher 1" } },
                TeacherDepartments = new List<TeacherDepartment>()
            };

            var validator = new ConfigValidator();

            await Assert.That(() => validator.ValidateAndNormalizeConfig(config))
                .Throws<InvalidOperationException>();
        }

        [Test]
        public async Task ValidateAndNormalizeConfig_NegativeSolverTimeLimit_UsesDefault()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday },
                BlocksPerDay = 5,
                Classes = new List<Class> { new Class { Key = "Math101", Department = "Math" } },
                Teachers = new List<Teacher> { new Teacher { Id = "T1", FullName = "Teacher 1" } },
                TeacherDepartments = new List<TeacherDepartment> { new TeacherDepartment { TeacherId = "T1", Department = "Math" } },
                SolverTimeLimitSeconds = -5.0
            };

            var validator = new ConfigValidator();
            var result = validator.ValidateAndNormalizeConfig(config);

            await Assert.That(result.SolverTimeLimitSeconds).IsEqualTo(10.0);
        }

        [Test]
        public async Task ValidateAndNormalizeConfig_NegativeRoomChangePenalty_UsesZero()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday },
                BlocksPerDay = 5,
                Classes = new List<Class> { new Class { Key = "Math101", Department = "Math" } },
                Teachers = new List<Teacher> { new Teacher { Id = "T1", FullName = "Teacher 1" } },
                TeacherDepartments = new List<TeacherDepartment> { new TeacherDepartment { TeacherId = "T1", Department = "Math" } },
                RoomChangePenalty = -5
            };

            var validator = new ConfigValidator();
            var result = validator.ValidateAndNormalizeConfig(config);

            await Assert.That(result.RoomChangePenalty).IsEqualTo(0);
        }

        [Test]
        public async Task ValidateAndNormalizeConfig_NegativeScheduleSpreadPenalty_UsesZero()
        {
            var config = new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday },
                BlocksPerDay = 5,
                Classes = new List<Class> { new Class { Key = "Math101", Department = "Math" } },
                Teachers = new List<Teacher> { new Teacher { Id = "T1", FullName = "Teacher 1" } },
                TeacherDepartments = new List<TeacherDepartment> { new TeacherDepartment { TeacherId = "T1", Department = "Math" } },
                ScheduleSpreadPenalty = -5
            };

            var validator = new ConfigValidator();
            var result = validator.ValidateAndNormalizeConfig(config);

            await Assert.That(result.ScheduleSpreadPenalty).IsEqualTo(0);
        }
    }
}
