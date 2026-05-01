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
                    Streams = new List<ClassStream>
                    {
                        new ClassStream { Id = "Sci101-Advanced", Size = 10, ProficiencyLevel = "Advanced", LinkedSubjects = new[] { "Science" } },
                        new ClassStream { Id = "Sci101-Basic", Size = 15, ProficiencyLevel = "Basic", LinkedSubjects = new[] { "Science" } }
                    }
                },
                new Class
                {
                    Key = "Math101",
                    Name = "Algebra",
                    Department = "Math",
                    PreferredRoom = "Room1",
                    WeeklyBlocks = 3,
                    Streams = new List<ClassStream>
                    {
                        new ClassStream { Id = "Math101-Advanced", Size = 12, ProficiencyLevel = "Advanced", LinkedSubjects = new[] { "Math" } }
                    }
                }
            };

            var streams = new List<ClassStream>
            {
                new ClassStream { Id = "Sci101-Advanced", Size = 10, ProficiencyLevel = "Advanced", LinkedSubjects = new[] { "Science" } },
                new ClassStream { Id = "Sci101-Basic", Size = 15, ProficiencyLevel = "Basic", LinkedSubjects = new[] { "Science" } },
                new ClassStream { Id = "Math101-Advanced", Size = 12, ProficiencyLevel = "Advanced", LinkedSubjects = new[] { "Math" } }
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
            // Realistic large secondary school scenario (grades 9-12)
            // Approximately 1600 students, 50+ teachers, 40+ classrooms
            // Subjects include core academics, electives, PE, and special programs

            var grades = new[] { "9", "10", "11" };
            var teachers = new List<Teacher>();
            var classes = new List<Class>();
            var streams = new List<ClassStream>();
            var rooms = new List<Room>();

            // Define subject configurations with realistic weekly blocks and class sizes
            var subjectConfigs = new (string Subject, string Dept, int WeeklyBlocks, int ClassSize, int CoursesPerGrade, string? Equipment, bool CoTeaching)[]
            {
                // Core subjects - meet 5x/week, moderate class sizes
                ("Math",        "Math",       5, 28, 2, null,  false),
                ("English",     "English",    5, 28, 2, null,  false),
                ("History",     "History",    5, 30, 1, null,  false),
                ("Geography",   "History",    5, 30, 1, null,  false),

                // Science - lab-based, smaller classes due to equipment
                ("Biology",     "Science",    5, 24, 1, "ScienceLab", false),
                ("Chemistry",   "Science",    5, 24, 1, "ScienceLab", false),
                ("Physics",     "Science",    5, 24, 1, "ScienceLab", false),

                // PE - large classes, gym required
                ("PE",          "PE",         5, 40, 1, "Gym",       false),
                ("Health",      "PE",         2, 35, 1, null,        false),

                // Arts - specialized rooms
                ("Art",         "Art",        5, 25, 1, "ArtStudio", false),
                ("Music",       "Art",        5, 30, 1, "MusicRoom", false),
                ("Drama",       "Art",        3, 28, 1, "Theater",   false),

                // Electives / Technology
                ("ComputerSci", "Technology", 5, 26, 1, "ComputerLab", false),
                ("Woodworking", "Technology", 3, 22, 1, "Woodshop",   false),
                ("AutoShop",    "Technology", 3, 20, 1, "AutoShop",   false),

                // Languages
                ("Spanish",     "Languages",  5, 26, 1, null,  false),
                ("French",      "Languages",  5, 24, 1, null,  false),

                // Special Programs
                ("SpecialEd",   "Special",    5, 12, 1, null,  true),
                ("ELL",         "Special",    5, 15, 1, null,  false)
            };

            // Generate specialized rooms based on equipment needs
            int roomId = 1;
            void AddRoom(string roomType, string equipment, int capacity)
            {
                rooms.Add(new Room
                {
                    Id = $"{roomType}{roomId}",
                    Capacity = capacity,
                    EquipmentType = "Standard",
                    IsShared = false,
                    SetupTimeBuffer = 0
                });
                roomId++;
            }

            // Standard classrooms (40 rooms)
            for (int i = 1; i <= 40; i++)
                AddRoom("Room", "Standard", 32);

            // Science labs (6 labs, 24 capacity each)
            for (int i = 1; i <= 6; i++)
                AddRoom("Lab", "ScienceLab", 24);

            // Computer labs (3 labs, 26 capacity)
            for (int i = 1; i <= 3; i++)
                AddRoom("CompLab", "ComputerLab", 26);

            // PE/gym facilities (2 gyms, 60 capacity)
            AddRoom("GymA", "Gym", 60);
            AddRoom("GymB", "Gym", 60);

            // Arts spaces
            AddRoom("Art1", "ArtStudio", 28);
            AddRoom("Art2", "ArtStudio", 28);
            AddRoom("Music1", "MusicRoom", 40);
            AddRoom("Music2", "MusicRoom", 40);
            AddRoom("Drama1", "Theater", 35);

            // Shop facilities
            AddRoom("Woodshop1", "Woodshop", 22);
            AddRoom("Autoshop1", "AutoShop", 20);

            // Generate teachers with specific course certifications
            int teacherId = 1;
            string[] allDepts = subjectConfigs.Select(s => s.Dept).Distinct().ToArray();

            // Create specialized teachers per department
            foreach (var dept in allDepts)
            {
                var deptConfigs = subjectConfigs.Where(s => s.Dept == dept).ToArray();
                int teachersInDept = dept switch
                {
                    "Math" => 12,
                    "English" => 12,
                    "Science" => 12,
                    "History" => 8,
                    "PE" => 8,
                    "Art" => 6,
                    "Technology" => 6,
                    "Languages" => 4,
                    "Special" => 6,
                    _ => 3
                };

                for (int t = 1; t <= teachersInDept; t++)
                {
                    // Assign each teacher a specific subject in round-robin fashion
                    var subjectIndex = (t - 1) % deptConfigs.Length;
                    var specificCourses = new[] { deptConfigs[subjectIndex].Subject };
                    string[] certs = specificCourses;

                    // All teachers use standard rooms
                    string prefEquip = "Standard";

                    var matchingRooms = rooms
                        .Where(r => r.EquipmentType == prefEquip || (prefEquip == "Standard" && r.EquipmentType == "Standard"))
                        .ToList();
                    var preferredRoom = matchingRooms.Count > 0
                        ? matchingRooms[(teacherId - 1) % matchingRooms.Count].Id
                        : "Room1";

                    teachers.Add(new Teacher
                    {
                        Id = $"T{teacherId}",
                        FullName = $"Teacher {teacherId}",
                        Email = $"teacher{teacherId}@school.edu",
                        PreferredRoom = preferredRoom,
                        Departments = new[] { dept },
                        TargetLoadBlocks = 25,
                        IsPartTime = teacherId % 10 == 0, // 10% part-time
                        Certifications = certs,
                        MaxConsecutiveBlocks = 4
                    });
                    teacherId++;
                }
            }

            // Build teacher-department mapping
            var teacherDepartments = teachers
                .SelectMany(t => t.Departments.Select(d => new TeacherDepartment { TeacherId = t.Id, Department = d }))
                .ToList();

            // Build dictionary of teachers by department for deterministic assignment
            var teachersByDept = teachers
                .SelectMany(t => t.Departments.Select(d => new { d, t }))
                .GroupBy(x => x.d, x => x.t, StringComparer.OrdinalIgnoreCase)
                .ToDictionary(g => g.Key, g => g.OrderBy(t => t.Id).ToList(), StringComparer.OrdinalIgnoreCase);
            var nextTeacherIndex = new Dictionary<string, int>(StringComparer.OrdinalIgnoreCase);

            // Generate classes and streams per grade
            int classId = 1;
            foreach (var grade in grades)
            {
                foreach (var (subject, dept, weeklyBlocks, classSize, coursesPerGrade, equipment, coTeaching) in subjectConfigs)
                {
                    // Grade-level restrictions
                    if (subject == "Physics" && (grade == "9" || grade == "10")) continue;
                    if (subject == "AutoShop" && (grade == "9" || grade == "12")) continue;
                    if (subject == "Drama" && (grade == "11" || grade == "12")) continue;

                    for (int c = 1; c <= coursesPerGrade; c++)
                    {
                        var clsKey = $"{subject}{grade}{c}";
                        var clsStreams = new List<ClassStream>();

                        int streamCount = coTeaching ? 2 : 1;
                        int studentsPerStream = classSize;

                        for (int s = 1; s <= streamCount; s++)
                        {
                            var streamId = $"{clsKey}-S{s}";
                            clsStreams.Add(new ClassStream
                            {
                                Id = streamId,
                                Size = studentsPerStream,
                                ProficiencyLevel = "Mixed",
                                LinkedSubjects = new[] { clsKey } // Unique per class to avoid cross-class subject conflicts
                            });
                            streams.Add(clsStreams.Last());
                        }

                        // Assign teachers deterministically using round-robin
                        if (!teachersByDept.TryGetValue(dept, out var deptTeachersList) || deptTeachersList.Count == 0)
                        {
                            throw new InvalidOperationException($"No teachers found for department '{dept}'.");
                        }

                        List<string> assignedTeacherIds;
                        if (coTeaching)
                        {
                            // For co-teaching (SpecialEd), assign first two teachers in the department
                            assignedTeacherIds = deptTeachersList.Take(2).Select(t => t.Id).ToList();
                        }
                        else
                        {
                            if (!nextTeacherIndex.ContainsKey(dept)) nextTeacherIndex[dept] = 0;
                            // For Special department, skip first two teachers reserved for SpecialEd co-teaching
                            if (dept == "Special" && nextTeacherIndex[dept] == 0)
                            {
                                nextTeacherIndex[dept] = 2;
                            }
                            int idx = nextTeacherIndex[dept] % deptTeachersList.Count;
                            assignedTeacherIds = new List<string> { deptTeachersList[idx].Id };
                            nextTeacherIndex[dept] = idx + 1;
                        }

                        // Find suitable room
                        string? roomEquipment = equipment;
                        if (string.IsNullOrEmpty(roomEquipment))
                        {
                            roomEquipment = dept switch
                            {
                                "PE" => "Gym",
                                "Art" => "ArtStudio",
                                "Languages" => "Standard",
                                _ => "Standard"
                            };
                        }

                        var preferredRoom = rooms
                            .FirstOrDefault(r => r.EquipmentType == roomEquipment)?.Id ?? "Room1";

                        var cls = new Class
                        {
                            Key = clsKey,
                            Name = $"{subject} {grade}.{c}",
                            Department = dept,
                            PreferredRoom = preferredRoom,
                            WeeklyBlocks = weeklyBlocks,
                            Streams = clsStreams,
                            TeacherIds = assignedTeacherIds
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
                TeacherDepartments = teacherDepartments,
                ScheduleType = BlockScheduleType.Traditional,
                AllowRoomSharing = true,
                SolverTimeLimitSeconds = 300,
                PresetBlocks = new List<PresetBlockConfig>(),
                // Disable penalties to speed up solving for this scenario
                RoomChangePenalty = 0,
                ScheduleSpreadPenalty = 0,
                WeekDistributionPenalty = 0,
                ClassDayClusteringPenalty = 0,
                ClassBlockConsistencyPenalty = 0,
                StreamFragmentationPenalty = 0,
                SharedRoomChangePenalty = 0,
                TargetLoadAdherencePenalty = 0,
                StudentRoomTransitionPenalty = 0,
                MergedBlockConsistencyPenalty = 0,
                FreeTimePenalty = 0,
                CommonPlanningPenalty = 0
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
            var streams = new List<ClassStream>();
            for (int i = 1; i <= scale * 3; i++)
            {
                var streamsList = new List<ClassStream>();
                for (int s = 1; s <= StreamCountPerClass; s++)
                {
                    var stream = new ClassStream
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