namespace SchedulePlanner.Core.Tests
{
    public static class SyntheticDataFactory
    {
        public static SchedulerOptions GenerateBasicScenario()
        {
            var teachers = new List<Teacher>
            {
                new Teacher { Id = "T1", FullName = "Alice Smith", Email = "alice@school.com", PreferredRoom = "Room1", Departments = new[] { "Math" }, TargetLoadBlocks = 20 },
                new Teacher { Id = "T2", FullName = "Bob Johnson", Email = "bob@school.com", PreferredRoom = "Room2", Departments = new[] { "English" }, TargetLoadBlocks = 18 },
                new Teacher { Id = "T3", FullName = "Carol Lee", Email = "carol@school.com", PreferredRoom = "Room3", Departments = new[] { "Science" }, TargetLoadBlocks = 22 }
            };

            var classes = new List<Class>
            {
                new Class { Key = "Math101", Name = "Algebra", Department = "Math", PreferredRoom = "Room1", WeeklyBlocks = 4 },
                new Class { Key = "Eng201", Name = "Literature", Department = "English", PreferredRoom = "Room2", WeeklyBlocks = 3 },
                new Class { Key = "Sci301", Name = "Biology", Department = "Science", PreferredRoom = "Room3", WeeklyBlocks = 5 }
            };

            var rooms = new List<Room>
            {
                new Room { Id = "Room1", Capacity = 25, EquipmentType = "Standard", IsShared = false, SetupTimeBuffer = 0 },
                new Room { Id = "Room2", Capacity = 30, EquipmentType = "Standard", IsShared = false, SetupTimeBuffer = 0 },
                new Room { Id = "Room3", Capacity = 20, EquipmentType = "Lab", IsShared = true, SetupTimeBuffer = 1 }
            };

            return new SchedulerOptions
            {
                Teachers = teachers,
                Classes = classes,
                Rooms = rooms
            };
        }

        public static SchedulerOptions GenerateStreamedScenario()
        {
            var teachers = new List<Teacher>
            {
                new Teacher { Id = "T1", FullName = "Alice Smith", Email = "alice@school.com", PreferredRoom = "Room1", Departments = new[] { "Math" }, TargetLoadBlocks = 20 },
                new Teacher { Id = "T2", FullName = "Bob Johnson", Email = "bob@school.com", PreferredRoom = "Room2", Departments = new[] { "English" }, TargetLoadBlocks = 18 },
                new Teacher { Id = "T3", FullName = "Carol Lee", Email = "carol@school.com", PreferredRoom = "Room3", Departments = new[] { "Science" }, TargetLoadBlocks = 22 }
            };

            var classes = new List<Class>
            {
                new Class
                {
                    Key = "Math101",
                    Name = "Algebra",
                    Department = "Math",
                    PreferredRoom = "Room1",
                    WeeklyBlocks = 4,
                    Streams = new List<ClassStream>
                    {
                        new ClassStream { Id = "Math101-Advanced", Size = 15, ProficiencyLevel = "Advanced", LinkedSubjects = new[] { "Math" } },
                        new ClassStream { Id = "Math101-Basic", Size = 20, ProficiencyLevel = "Basic", LinkedSubjects = new[] { "Math" } }
                    }
                },
                new Class
                {
                    Key = "Eng201",
                    Name = "Literature",
                    Department = "English",
                    PreferredRoom = "Room2",
                    WeeklyBlocks = 3,
                    Streams = new List<ClassStream>
                    {
                        new ClassStream { Id = "Eng201-Advanced", Size = 12, ProficiencyLevel = "Advanced", LinkedSubjects = new[] { "English" } },
                        new ClassStream { Id = "Eng201-Basic", Size = 18, ProficiencyLevel = "Basic", LinkedSubjects = new[] { "English" } }
                    }
                }
            };

            var streams = new List<ClassStream>
            {
                new ClassStream { Id = "Math101-Advanced", Size = 15, ProficiencyLevel = "Advanced", LinkedSubjects = new[] { "Math" } },
                new ClassStream { Id = "Math101-Basic", Size = 20, ProficiencyLevel = "Basic", LinkedSubjects = new[] { "Math" } },
                new ClassStream { Id = "Eng201-Advanced", Size = 12, ProficiencyLevel = "Advanced", LinkedSubjects = new[] { "English" } },
                new ClassStream { Id = "Eng201-Basic", Size = 18, ProficiencyLevel = "Basic", LinkedSubjects = new[] { "English" } }
            };

            var rooms = new List<Room>
            {
                new Room { Id = "Room1", Capacity = 25, EquipmentType = "Standard", IsShared = false, SetupTimeBuffer = 0 },
                new Room { Id = "Room2", Capacity = 30, EquipmentType = "Standard", IsShared = false, SetupTimeBuffer = 0 },
                new Room { Id = "Room3", Capacity = 20, EquipmentType = "Lab", IsShared = true, SetupTimeBuffer = 1 }
            };

            return new SchedulerOptions
            {
                Teachers = teachers,
                Classes = classes,
                Streams = streams,
                Rooms = rooms
            };
        }

        public static SchedulerOptions GenerateBlockPeriodScenario()
        {
            var teachers = new List<Teacher>
            {
                new Teacher { Id = "T1", FullName = "Alice Smith", Email = "alice@school.com", PreferredRoom = "Room1", Departments = new[] { "Math" }, TargetLoadBlocks = 20 },
                new Teacher { Id = "T2", FullName = "Bob Johnson", Email = "bob@school.com", PreferredRoom = "Room2", Departments = new[] { "English" }, TargetLoadBlocks = 18 }
            };

            var classes = new List<Class>
            {
                new Class { Key = "Math101", Name = "Algebra", Department = "Math", PreferredRoom = "Room1", WeeklyBlocks = 6 },
                new Class { Key = "Eng201", Name = "Literature", Department = "English", PreferredRoom = "Room2", WeeklyBlocks = 4 }
            };

            var rooms = new List<Room>
            {
                new Room { Id = "Room1", Capacity = 25, EquipmentType = "Standard", IsShared = false, SetupTimeBuffer = 0 },
                new Room { Id = "Room2", Capacity = 30, EquipmentType = "Standard", IsShared = false, SetupTimeBuffer = 0 }
            };

            var mergedBlocks = new List<MergedBlock>
            {
                new MergedBlock(new[] { 0, 1 }), // Double block for first two
                new MergedBlock(new[] { 4, 5 })  // Double block for last two
            };

            return new SchedulerOptions
            {
                Teachers = teachers,
                Classes = classes,
                Rooms = rooms,
                ScheduleType = BlockScheduleType.ABAlternating,
                MergedBlocks = mergedBlocks
            };
        }

        public static SchedulerOptions GenerateSharedClassroomScenario()
        {
            var teachers = new List<Teacher>
            {
                new Teacher { Id = "T1", FullName = "Alice Smith", Email = "alice@school.com", PreferredRoom = "Lab1", Departments = new[] { "Science" }, TargetLoadBlocks = 20 },
                new Teacher { Id = "T2", FullName = "Bob Johnson", Email = "bob@school.com", PreferredRoom = "Lab1", Departments = new[] { "Science" }, TargetLoadBlocks = 18 },
                new Teacher { Id = "T3", FullName = "Carol Lee", Email = "carol@school.com", PreferredRoom = "Room1", Departments = new[] { "Math" }, TargetLoadBlocks = 22 }
            };

            var classes = new List<Class>
            {
                new Class { Key = "Sci101", Name = "Chemistry", Department = "Science", PreferredRoom = "Lab1", WeeklyBlocks = 4 },
                new Class { Key = "Sci201", Name = "Physics", Department = "Science", PreferredRoom = "Lab1", WeeklyBlocks = 4 },
                new Class { Key = "Math101", Name = "Algebra", Department = "Math", PreferredRoom = "Room1", WeeklyBlocks = 3 }
            };

            var rooms = new List<Room>
            {
                new Room { Id = "Lab1", Capacity = 20, EquipmentType = "Lab", IsShared = true, SetupTimeBuffer = 1 },
                new Room { Id = "Room1", Capacity = 30, EquipmentType = "Standard", IsShared = false, SetupTimeBuffer = 0 }
            };

            return new SchedulerOptions
            {
                Teachers = teachers,
                Classes = classes,
                Rooms = rooms
            };
        }

        public static SchedulerOptions GenerateCombinedScenario()
        {
            var teachers = new List<Teacher>
            {
                new Teacher { Id = "T1", FullName = "Alice Smith", Email = "alice@school.com", PreferredRoom = "Lab1", Departments = new[] { "Science" }, TargetLoadBlocks = 25, IsPartTime = false, Certifications = new[] { "Science" }, MaxConsecutiveBlocks = 3 },
                new Teacher { Id = "T2", FullName = "Bob Johnson", Email = "bob@school.com", PreferredRoom = "Lab1", Departments = new[] { "Science" }, TargetLoadBlocks = 15, IsPartTime = true, Certifications = new[] { "Science" }, MaxConsecutiveBlocks = 2 },
                new Teacher { Id = "T3", FullName = "Carol Lee", Email = "carol@school.com", PreferredRoom = "Room1", Departments = new[] { "Math", "English" }, TargetLoadBlocks = 20, IsPartTime = false, Certifications = new[] { "Math", "English" }, MaxConsecutiveBlocks = 4 }
            };

            var classes = new List<Class>
            {
                new Class
                {
                    Key = "Sci101",
                    Name = "Chemistry",
                    Department = "Science",
                    PreferredRoom = "Lab1",
                    WeeklyBlocks = 4,
                    Streams = new List<Stream>
                    {
                        new Stream { Id = "Sci101-Advanced", Size = 10, ProficiencyLevel = "Advanced", LinkedSubjects = new[] { "Science" } },
                        new Stream { Id = "Sci101-Basic", Size = 15, ProficiencyLevel = "Basic", LinkedSubjects = new[] { "Science" } }
                    }
                },
                new Class
                {
                    Key = "Math101",
                    Name = "Algebra",
                    Department = "Math",
                    PreferredRoom = "Room1",
                    WeeklyBlocks = 3,
                    Streams = new List<Stream>
                    {
                        new Stream { Id = "Math101-Advanced", Size = 12, ProficiencyLevel = "Advanced", LinkedSubjects = new[] { "Math" } }
                    }
                }
            };

            var streams = new List<Stream>
            {
                new Stream { Id = "Sci101-Advanced", Size = 10, ProficiencyLevel = "Advanced", LinkedSubjects = new[] { "Science" } },
                new Stream { Id = "Sci101-Basic", Size = 15, ProficiencyLevel = "Basic", LinkedSubjects = new[] { "Science" } },
                new Stream { Id = "Math101-Advanced", Size = 12, ProficiencyLevel = "Advanced", LinkedSubjects = new[] { "Math" } }
            };

            var rooms = new List<Room>
            {
                new Room { Id = "Lab1", Capacity = 20, EquipmentType = "Lab", IsShared = true, SetupTimeBuffer = 1 },
                new Room { Id = "Room1", Capacity = 30, EquipmentType = "Standard", IsShared = false, SetupTimeBuffer = 0 }
            };

            var mergedBlocks = new List<MergedBlock>
            {
                new MergedBlock(new[] { 2, 3 }) // Double block
            };

            return new SchedulerOptions
            {
                Teachers = teachers,
                Classes = classes,
                Streams = streams,
                Rooms = rooms,
                ScheduleType = BlockScheduleType.ABAlternating,
                MergedBlocks = mergedBlocks
            };
        }

        public static SchedulerOptions GenerateLargeK12School()
        {
            // Demo for 1600 students
            // Assume 4 grades, 400 per grade
            // Subjects: Math, English, Science, History, PE, Art
            // Classes per grade per subject: 4-5
            // Streams: 2-3 per class
            // Teachers: 50-60
            // Rooms: 40-50

            var departments = new[] { "Math", "English", "Science", "History", "PE", "Art" };
            var grades = new[] { "9", "10", "11", "12" };
            var teachers = new List<Teacher>();
            var classes = new List<Class>();
            var streams = new List<Stream>();
            var rooms = new List<Room>();

            // Generate rooms
            for (int i = 1; i <= 50; i++)
            {
                rooms.Add(new Room { Id = $"Room{i}", Capacity = 30, EquipmentType = i % 5 == 0 ? "Lab" : "Standard", IsShared = i % 10 == 0, SetupTimeBuffer = i % 10 == 0 ? 1 : 0 });
            }

            // Generate teachers
            for (int i = 1; i <= 60; i++)
            {
                var dept = departments[i % departments.Length];
                teachers.Add(new Teacher
                {
                    Id = $"T{i}",
                    FullName = $"Teacher {i}",
                    Email = $"teacher{i}@school.com",
                    PreferredRoom = $"Room{i % 50 + 1}",
                    Departments = new[] { dept },
                    TargetLoadBlocks = 25,
                    IsPartTime = i % 10 == 0,
                    Certifications = new[] { dept },
                    MaxConsecutiveBlocks = 4
                });
            }

            // Generate classes and streams
            int classId = 1;
            foreach (var grade in grades)
            {
                foreach (var dept in departments)
                {
                    for (int c = 1; c <= 4; c++) // 4 classes per grade per subject
                    {
                        var clsKey = $"{dept}{grade}{c}";
                        var clsStreams = new List<Stream>();
                        for (int s = 1; s <= 2; s++) // 2 streams per class
                        {
                            var streamId = $"{clsKey}-Stream{s}";
                            var stream = new Stream
                            {
                                Id = streamId,
                                Size = 20, // approx 400 / 4 / 2 / 2.5 wait, adjust
                                ProficiencyLevel = s == 1 ? "Advanced" : "Basic",
                                LinkedSubjects = new[] { dept }
                            };
                            clsStreams.Add(stream);
                            streams.Add(stream);
                        }
                        var cls = new Class
                        {
                            Key = clsKey,
                            Name = $"{dept} {grade}.{c}",
                            Department = dept,
                            PreferredRoom = $"Room{classId % 50 + 1}",
                            WeeklyBlocks = 5,
                            Streams = clsStreams
                        };
                        classes.Add(cls);
                        classId++;
                    }
                }
            }

            return new SchedulerOptions
            {
                Days = new[] { DayOfWeek.Monday, DayOfWeek.Tuesday, DayOfWeek.Wednesday, DayOfWeek.Thursday, DayOfWeek.Friday },
                BlocksPerDay = 8,
                Teachers = teachers,
                Classes = classes,
                Streams = streams,
                Rooms = rooms,
                ScheduleType = BlockScheduleType.Traditional
            };
        }
    }

    public class SyntheticDataBuilder
    {
        public int SchoolSize { get; set; } = 400;
        public int StreamCountPerClass { get; set; } = 2;
        public int BlockComplexity { get; set; } = 1; // 1 = simple, 2 = merged, 3 = complex

        public SchedulerOptions Build()
        {
            // Simple implementation: scale the basic scenario
            var scale = Math.Max(1, SchoolSize / 100); // approx

            var teachers = new List<Teacher>();
            for (int i = 1; i <= scale * 3; i++)
            {
                teachers.Add(new Teacher
                {
                    Id = $"T{i}",
                    FullName = $"Teacher {i}",
                    Email = $"teacher{i}@school.com",
                    PreferredRoom = $"Room{i % (scale * 3) + 1}",
                    Departments = new[] { i % 3 == 0 ? "Math" : i % 3 == 1 ? "English" : "Science" },
                    TargetLoadBlocks = 20
                });
            }

            var classes = new List<Class>();
            var streams = new List<Stream>();
            for (int i = 1; i <= scale * 3; i++)
            {
                var streamsList = new List<Stream>();
                for (int s = 1; s <= StreamCountPerClass; s++)
                {
                    var stream = new Stream
                    {
                        Id = $"C{i}-S{s}",
                        Size = SchoolSize / (scale * 3 * StreamCountPerClass),
                        ProficiencyLevel = s == 1 ? "Advanced" : "Basic",
                        LinkedSubjects = new[] { i % 3 == 0 ? "Math" : i % 3 == 1 ? "English" : "Science" }
                    };
                    streamsList.Add(stream);
                    streams.Add(stream);
                }
                classes.Add(new Class
                {
                    Key = $"C{i}",
                    Name = $"Class {i}",
                    Department = i % 3 == 0 ? "Math" : i % 3 == 1 ? "English" : "Science",
                    PreferredRoom = $"Room{i % (scale * 3) + 1}",
                    WeeklyBlocks = 4,
                    Streams = streamsList
                });
            }

            var rooms = new List<Room>();
            for (int i = 1; i <= scale * 3; i++)
            {
                rooms.Add(new Room
                {
                    Id = $"Room{i}",
                    Capacity = 30,
                    EquipmentType = "Standard",
                    IsShared = false,
                    SetupTimeBuffer = 0
                });
            }

            var mergedBlocks = BlockComplexity >= 2 ? new List<MergedBlock> { new MergedBlock(new[] { 0, 1 }) } : new List<MergedBlock>();

            return new SchedulerOptions
            {
                Teachers = teachers,
                Classes = classes,
                Streams = streams,
                Rooms = rooms,
                MergedBlocks = mergedBlocks,
                ScheduleType = BlockComplexity >= 2 ? BlockScheduleType.ABAlternating : BlockScheduleType.Traditional
            };
        }
    }
}