namespace SchedulePlanner.Core.Tests
{
    public class ClassAssignmentBuilderTests
    {
        [Test]
        public async Task BuildClassAssignments_ValidConfig_ReturnsAssignments()
        {
            var config = new SchedulerOptions
            {
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math", Name = "Algebra" },
                    new Class { Key = "Sci101", Department = "Science", Name = "Physics" }
                },
                Teachers = new List<Teacher>
                {
                    new Teacher { Id = "T1", FullName = "Teacher 1", PreferredRoom = "Room101" },
                    new Teacher { Id = "T2", FullName = "Teacher 2", PreferredRoom = "Room102" }
                },
                TeacherDepartments = new List<TeacherDepartment>
                {
                    new TeacherDepartment { TeacherId = "T1", Department = "Math" },
                    new TeacherDepartment { TeacherId = "T2", Department = "Science" }
                }
            };

            var builder = new ClassAssignmentBuilder();
            var assignments = builder.BuildClassAssignments(config);

            await Assert.That(assignments).IsNotNull();
            await Assert.That(assignments.Count).IsEqualTo(2);
            await Assert.That(assignments[0].Config.Key).IsEqualTo("Math101");
            await Assert.That(assignments[0].Teacher.Id).IsEqualTo("T1");
            await Assert.That(assignments[0].Room).IsEqualTo("Room101");
            await Assert.That(assignments[1].Config.Key).IsEqualTo("Sci101");
            await Assert.That(assignments[1].Teacher.Id).IsEqualTo("T2");
            await Assert.That(assignments[1].Room).IsEqualTo("Room102");
        }

        [Test]
        public async Task BuildClassAssignments_ClassWithPreferredRoom_UsesClassRoom()
        {
            var config = new SchedulerOptions
            {
                Classes = new List<Class>
                {
                    new Class { Key = "Calc101", Department = "Math", PreferredRoom = "Room102" }
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

            var builder = new ClassAssignmentBuilder();
            var assignments = builder.BuildClassAssignments(config);

            await Assert.That(assignments[0].Room).IsEqualTo("Room101");
        }

        [Test]
        public async Task BuildClassAssignments_NoKey_ThrowsException()
        {
            var config = new SchedulerOptions
            {
                Classes = new List<Class>
                {
                    new Class { Key = "", Department = "Math" }
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

            var builder = new ClassAssignmentBuilder();

            await Assert.That(() => builder.BuildClassAssignments(config))
                .Throws<InvalidOperationException>();
        }

        [Test]
        public async Task BuildClassAssignments_NoDepartment_ThrowsException()
        {
            var config = new SchedulerOptions
            {
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "" }
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

            var builder = new ClassAssignmentBuilder();

            await Assert.That(() => builder.BuildClassAssignments(config))
                .Throws<InvalidOperationException>();
        }

        [Test]
        public async Task BuildClassAssignments_NoTeacherForDepartment_ThrowsException()
        {
            var config = new SchedulerOptions
            {
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math" }
                },
                Teachers = new List<Teacher>
                {
                    new Teacher { Id = "T1", FullName = "Teacher 1" }
                },
                TeacherDepartments = new List<TeacherDepartment>
                {
                    new TeacherDepartment { TeacherId = "T1", Department = "Science" }
                }
            };

            var builder = new ClassAssignmentBuilder();

            await Assert.That(() => builder.BuildClassAssignments(config))
                .Throws<InvalidOperationException>();
        }

        [Test]
        public async Task BuildClassAssignments_MultipleTeachersForDepartment_ThrowsException()
        {
            var config = new SchedulerOptions
            {
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math" }
                },
                Teachers = new List<Teacher>
                {
                    new Teacher { Id = "T1", FullName = "Teacher 1" },
                    new Teacher { Id = "T2", FullName = "Teacher 2" }
                },
                TeacherDepartments = new List<TeacherDepartment>
                {
                    new TeacherDepartment { TeacherId = "T1", Department = "Math" },
                    new TeacherDepartment { TeacherId = "T2", Department = "Math" }
                }
            };

            var builder = new ClassAssignmentBuilder();

            await Assert.That(() => builder.BuildClassAssignments(config))
                .Throws<InvalidOperationException>();
        }

        [Test]
        public async Task BuildClassAssignments_UnknownTeacher_ThrowsException()
        {
            var config = new SchedulerOptions
            {
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math" }
                },
                Teachers = new List<Teacher>
                {
                    new Teacher { Id = "T1", FullName = "Teacher 1" }
                },
                TeacherDepartments = new List<TeacherDepartment>
                {
                    new TeacherDepartment { TeacherId = "T2", Department = "Math" }
                }
            };

            var builder = new ClassAssignmentBuilder();

            await Assert.That(() => builder.BuildClassAssignments(config))
                .Throws<InvalidOperationException>();
        }

        [Test]
        public async Task BuildClassAssignments_NoRoom_ThrowsException()
        {
            var config = new SchedulerOptions
            {
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math" }
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

            var builder = new ClassAssignmentBuilder();

            await Assert.That(() => builder.BuildClassAssignments(config))
                .Throws<InvalidOperationException>();
        }

        [Test]
        public async Task BuildTeacherGroups_ValidAssignments_ReturnsGroups()
        {
            var config = new SchedulerOptions
            {
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math" },
                    new Class { Key = "Math102", Department = "Math" }
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

            var builder = new ClassAssignmentBuilder();
            var assignments = builder.BuildClassAssignments(config);
            var groups = builder.BuildTeacherGroups(assignments);

            await Assert.That(groups).IsNotNull();
            await Assert.That(groups.Count).IsEqualTo(1);
            await Assert.That(groups.ContainsKey("T1")).IsTrue();
            await Assert.That(groups["T1"].Classes.Count).IsEqualTo(2);
        }

        [Test]
        public async Task BuildRoomGroups_ValidAssignments_ReturnsGroups()
        {
            var config = new SchedulerOptions
            {
                Classes = new List<Class>
                {
                    new Class { Key = "Math101", Department = "Math" },
                    new Class { Key = "Sci101", Department = "Science" }
                },
                Teachers = new List<Teacher>
                {
                    new Teacher { Id = "T1", FullName = "Teacher 1", PreferredRoom = "Room101" },
                    new Teacher { Id = "T2", FullName = "Teacher 2", PreferredRoom = "Room101" }
                },
                TeacherDepartments = new List<TeacherDepartment>
                {
                    new TeacherDepartment { TeacherId = "T1", Department = "Math" },
                    new TeacherDepartment { TeacherId = "T2", Department = "Science" }
                }
            };

            var builder = new ClassAssignmentBuilder();
            var assignments = builder.BuildClassAssignments(config);
            var groups = builder.BuildRoomGroups(assignments);

            await Assert.That(groups).IsNotNull();
            await Assert.That(groups.Count).IsEqualTo(1);
            await Assert.That(groups.ContainsKey("Room101")).IsTrue();
            await Assert.That(groups["Room101"].Count).IsEqualTo(2);
        }
    }
}
