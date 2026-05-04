namespace SchedulePlanner.Core;

public static class DemoDataFactory
{
    /// <summary>
    /// Creates a realistic small K12 school demo scheduler options for testing.
    /// Approximately 200 students, 10 teachers, 8 classrooms.
    /// </summary>
    public static SchedulerOptions CreateSmallK12SchoolDemo()
    {
        // Small school scenario for testing - grades 9-10
        var grades = new[] { "9", "10" };
        var teachers = new List<Teacher>();
        var classes = new List<Class>();
        var streams = new List<ClassStream>();
        var rooms = new List<Room>();

        // Reduced subject configurations
        var subjectConfigs = new (string Subject, string Dept, int WeeklyBlocks, int ClassSize, int CoursesPerGrade, string? Equipment, bool CoTeaching)[]
        {
            ("Math", "Math", 4, 25, 1, null, false),
            ("English", "English", 4, 25, 1, null, false),
            ("History", "History", 4, 25, 1, null, false),
            ("Science", "Science", 4, 20, 1, "ScienceLab", false),
            ("PE", "PE", 4, 30, 1, "Gym", false),
        };

        int roomId = 1;
        void AddRoom(string roomType, string equipment, int capacity)
        {
            rooms.Add(new Room
            {
                Id = $"{roomType}{roomId:D2}",
                Capacity = capacity,
                EquipmentType = equipment,
                IsShared = false,
                SetupTimeBuffer = equipment == "ScienceLab" ? 2 : 0
            });
            roomId++;
        }

        // Standard classrooms (6 rooms)
        for (int i = 1; i <= 6; i++)
            AddRoom("Room", "Standard", 30);

        // Science labs (1 lab)
        AddRoom("Lab", "ScienceLab", 20);

        // PE/gym facilities
        AddRoom("GymA", "Gym", 40);

        // Generate teachers (10 total)
        int teacherId = 1;
        string[] allDepts = subjectConfigs.Select(s => s.Dept).Distinct().ToArray();

        foreach (var dept in allDepts)
        {
            var deptConfigs = subjectConfigs.Where(s => s.Dept == dept).ToArray();
            int teachersInDept = dept switch
            {
                "Math" => 2,
                "English" => 2,
                "Science" => 2,
                "History" => 2,
                "PE" => 2,
                _ => 1
            };

            for (int t = 1; t <= teachersInDept; t++)
            {
                var subjectIndex = (t - 1) % deptConfigs.Length;
                var specificCourses = new[] { deptConfigs[subjectIndex].Subject };
                string[] certs = specificCourses;

                teachers.Add(new Teacher
                {
                    Id = $"T{teacherId:D2}",
                    FullName = $"Teacher {teacherId:D2}",
                    Email = $"teacher{teacherId:D2}@school.edu",
                    PreferredRoom = "Room01",
                    Departments = new[] { dept },
                    TargetLoadBlocks = 18 + (teacherId % 3),
                    IsPartTime = false,
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

        // Build dictionary of teachers by department
        var teachersByDept = teachers
            .SelectMany(t => t.Departments.Select(d => new { d, t }))
            .GroupBy(x => x.d, x => x.t, StringComparer.OrdinalIgnoreCase)
            .ToDictionary(g => g.Key, g => g.OrderBy(t => t.Id).ToList(), StringComparer.OrdinalIgnoreCase);
        var nextTeacherIndex = new Dictionary<string, int>(StringComparer.OrdinalIgnoreCase);

        // Generate classes
        int classId = 1;
        foreach (var grade in grades)
        {
            foreach (var (subject, dept, weeklyBlocks, classSize, coursesPerGrade, equipment, coTeaching) in subjectConfigs)
            {
                for (int c = 1; c <= coursesPerGrade; c++)
                {
                    var clsKey = $"{subject}{grade}{c}";
                    var clsStreams = new List<ClassStream>();

                    int streamCount = 1;
                    int studentsPerStream = classSize;

                    for (int s = 1; s <= streamCount; s++)
                    {
                        var streamId = $"{clsKey}-S{s}";
                        clsStreams.Add(new ClassStream
                        {
                            Id = streamId,
                            Size = studentsPerStream,
                            ProficiencyLevel = "Mixed",
                            LinkedSubjects = new[] { subject }
                        });
                        streams.Add(clsStreams.Last());
                    }

                    // Assign teachers
                    if (!teachersByDept.TryGetValue(dept, out var deptTeachersList) || deptTeachersList.Count == 0)
                    {
                        throw new InvalidOperationException($"No teachers found for department '{dept}'.");
                    }

                    if (!nextTeacherIndex.ContainsKey(dept)) nextTeacherIndex[dept] = 0;
                    int idx = nextTeacherIndex[dept] % deptTeachersList.Count;
                    var assignedTeacherIds = new List<string> { deptTeachersList[idx].Id };
                    nextTeacherIndex[dept] = idx + 1;

                    string? roomEquipment = equipment ?? "Standard";

                    var preferredRoom = rooms
                        .FirstOrDefault(r => r.EquipmentType == roomEquipment)?.Id ?? "Room01";

                    classes.Add(new Class
                    {
                        Key = clsKey,
                        Name = $"{subject} {grade}.{c}",
                        Department = dept,
                        PreferredRoom = preferredRoom,
                        WeeklyBlocks = weeklyBlocks,
                        Streams = clsStreams,
                        TeacherIds = assignedTeacherIds
                    });
                    classId++;
                }
            }
        }

        return new SchedulerOptions
        {
            Days = SchedulerOptions.MonTueWedThuFri,
            BlocksPerDay = 7,
            Teachers = teachers,
            Classes = classes,
            Streams = streams,
            Rooms = rooms,
            TeacherDepartments = teacherDepartments,
            ScheduleType = BlockScheduleType.Traditional,
            AllowRoomSharing = true,
            SolverTimeLimitSeconds = 30,
            RoomChangePenalty = 3,
            ScheduleSpreadPenalty = 2,
            WeekDistributionPenalty = 1,
            ClassDayClusteringPenalty = 1,
            ClassBlockConsistencyPenalty = 1,
            StreamFragmentationPenalty = 1,
            SharedRoomChangePenalty = 3,
            TargetLoadAdherencePenalty = 2,
            StudentRoomTransitionPenalty = 2,
            MergedBlockConsistencyPenalty = 1,
            FreeTimePenalty = 1,
            CommonPlanningPenalty = 1
        };
    }

    /// <summary>
    /// Creates an unsolvable demo to test progress timeout - too many classes for available time slots.
    /// </summary>
    public static SchedulerOptions CreateUnsolvableDemo()
    {
        // Create a scenario with more classes than available time slots to make it unsolvable
        var teachers = new List<Teacher>();
        var classes = new List<Class>();
        var streams = new List<ClassStream>();
        var rooms = new List<Room>();

        // Only 1 room available
        rooms.Add(new Room
        {
            Id = "Room1",
            Capacity = 30,
            EquipmentType = "Standard",
            IsShared = false,
            SetupTimeBuffer = 0
        });

        // Only 2 teachers available
        teachers.Add(new Teacher
        {
            Id = "T1",
            FullName = "Teacher 1",
            Email = "teacher1@school.edu",
            PreferredRoom = "Room1",
            Departments = new[] { "Math" },
            TargetLoadBlocks = 20,
            IsPartTime = false,
            Certifications = new[] { "Math" },
            MaxConsecutiveBlocks = 4
        });

        teachers.Add(new Teacher
        {
            Id = "T2",
            FullName = "Teacher 2",
            Email = "teacher2@school.edu",
            PreferredRoom = "Room1",
            Departments = new[] { "English" },
            TargetLoadBlocks = 20,
            IsPartTime = false,
            Certifications = new[] { "English" },
            MaxConsecutiveBlocks = 4
        });

        var teacherDepartments = teachers
            .SelectMany(t => t.Departments.Select(d => new TeacherDepartment { TeacherId = t.Id, Department = d }))
            .ToList();

        // Create way too many classes for the available time (5 days × 7 blocks = 35 slots, but we'll create 50+ classes)
        int classId = 1;
        for (int i = 1; i <= 30; i++) // 30 classes - way more than 35 available slots
        {
            var subject = i % 2 == 0 ? "Math" : "English";
            var teacherId = subject == "Math" ? "T1" : "T2";

            var clsKey = $"{subject}{i}";
            var clsStreams = new List<ClassStream>
            {
                new ClassStream
                {
                    Id = $"{clsKey}-S1",
                    Size = 25,
                    ProficiencyLevel = "Mixed",
                    LinkedSubjects = new[] { subject }
                }
            };
            streams.Add(clsStreams[0]);

            classes.Add(new Class
            {
                Key = clsKey,
                Name = $"{subject} Class {i}",
                Department = subject,
                PreferredRoom = "Room1",
                WeeklyBlocks = 1, // Each class needs 1 block per week
                Streams = clsStreams,
                TeacherIds = new List<string> { teacherId }
            });
            classId++;
        }

        return new SchedulerOptions
        {
            Days = SchedulerOptions.MonTueWedThuFri,
            BlocksPerDay = 7, // 5 days × 7 blocks = 35 total slots
            Teachers = teachers,
            Classes = classes, // 30 classes needing 30 slots, but only 35 available and teachers have constraints
            Streams = streams,
            Rooms = rooms, // Only 1 room
            TeacherDepartments = teacherDepartments,
            ScheduleType = BlockScheduleType.Traditional,
            AllowRoomSharing = false, // No room sharing makes it even harder
            SolverTimeLimitSeconds = 300, // Long time limit so timeout triggers first
            RoomChangePenalty = 10, // High penalty to make scheduling harder
            ScheduleSpreadPenalty = 10,
            WeekDistributionPenalty = 10,
            ClassDayClusteringPenalty = 10,
            ClassBlockConsistencyPenalty = 10,
            StreamFragmentationPenalty = 10,
            SharedRoomChangePenalty = 10,
            TargetLoadAdherencePenalty = 10,
            StudentRoomTransitionPenalty = 10,
            MergedBlockConsistencyPenalty = 10,
            FreeTimePenalty = 10,
            CommonPlanningPenalty = 10
        };
    }

    /// <summary>
    /// Creates a realistic large K12 school demo scheduler options.
    /// Approximately 1600 students, 50+ teachers, 40+ classrooms.
    /// </summary>
    public static SchedulerOptions CreateLargeK12SchoolDemo()
    {
         // Realistic large secondary school scenario (grades 9-12)
         // Approximately 1600 students, 40 teachers, 35 classrooms
         var grades = new[] { "9", "10", "11" };
         var teachers = new List<Teacher>();
         var classes = new List<Class>();
         var streams = new List<ClassStream>();
         var rooms = new List<Room>();

         // Define subject configurations with realistic weekly blocks and class sizes
         // Reduced blocks/week to make problem feasible within preset block constraints
         var subjectConfigs = new (string Subject, string Dept, int WeeklyBlocks, int ClassSize, int CoursesPerGrade, string? Equipment, bool CoTeaching)[]
         {
             // Core subjects - meet 4x/week, moderate class sizes (reduced from 5)
             ("Math",        "Math",       4, 28, 2, null,  false),
             ("English",     "English",    4, 28, 2, null,  false),
             ("History",     "History",    4, 30, 1, null,  false),
             ("Geography",   "History",    4, 30, 1, null,  false),

             // Science - lab-based, smaller classes due to equipment
             ("Biology",     "Science",    4, 24, 1, "ScienceLab", false),
             ("Chemistry",   "Science",    4, 24, 1, "ScienceLab", false),
             ("Physics",     "Science",    4, 24, 1, "ScienceLab", false),

             // PE - large classes, gym required
             ("PE",          "PE",         4, 40, 1, "Gym",       false),
             ("Health",      "PE",         2, 35, 1, null,        false),

             // Arts - specialized rooms
             ("Art",         "Art",        4, 25, 1, "ArtStudio", false),
             ("Music",       "Art",        4, 30, 1, "MusicRoom", false),
             ("Drama",       "Art",        3, 28, 1, "Theater",   false),

             // Electives / Technology
             ("ComputerSci", "Technology", 4, 26, 1, "ComputerLab", false),
             ("Woodworking", "Technology", 3, 22, 1, "Woodshop",   false),
             ("AutoShop",    "Technology", 3, 20, 1, "AutoShop",   false),

             // Languages
             ("Spanish",     "Languages",  4, 26, 1, null,  false),
             ("French",      "Languages",  4, 24, 1, null,  false),

             // Special Programs
             ("SpecialEd",   "Special",    4, 12, 1, null,  true),
             ("ELL",         "Special",    4, 15, 1, null,  false)
         };

         int roomId = 1;
         void AddRoom(string roomType, string equipment, int capacity)
         {
             rooms.Add(new Room
             {
                 Id = $"{roomType}{roomId:D2}",
                 Capacity = capacity,
                 EquipmentType = equipment,
                 IsShared = false,
                 SetupTimeBuffer = equipment == "ScienceLab" || equipment == "ComputerLab" ? 2 : 0
             });
             roomId++;
         }

         // Standard classrooms (35 rooms, slightly reduced)
         for (int i = 1; i <= 35; i++)
             AddRoom("Room", "Standard", 32);

         // Science labs (4 labs, reduced from 6)
         for (int i = 1; i <= 4; i++)
             AddRoom("Lab", "ScienceLab", 24);

         // Computer labs (2 labs, reduced from 3)
         for (int i = 1; i <= 2; i++)
             AddRoom("CompLab", "ComputerLab", 26);

         // PE/gym facilities
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

         // Create specialized teachers per department (slightly reduced)
         foreach (var dept in allDepts)
         {
             var deptConfigs = subjectConfigs.Where(s => s.Dept == dept).ToArray();
             int teachersInDept = dept switch
             {
                 "Math" => 10,
                 "English" => 10,
                 "Science" => 8,
                 "History" => 6,
                 "PE" => 6,
                 "Art" => 4,
                 "Technology" => 4,
                 "Languages" => 3,
                 "Special" => 4,
                 _ => 3
             };

             for (int t = 1; t <= teachersInDept; t++)
             {
                 var subjectIndex = (t - 1) % deptConfigs.Length;
                 var specificCourses = new[] { deptConfigs[subjectIndex].Subject };
                 string[] certs = specificCourses;

                 string prefEquip = "Standard";

                 var matchingRooms = rooms
                     .Where(r => r.EquipmentType == prefEquip || (prefEquip == "Standard" && r.EquipmentType == "Standard"))
                     .ToList();
                 var preferredRoom = matchingRooms.Count > 0
                     ? matchingRooms[(teacherId - 1) % matchingRooms.Count].Id
                     : "Room01";

                 teachers.Add(new Teacher
                 {
                     Id = $"T{teacherId:D2}",
                     FullName = $"Teacher {teacherId:D2}",
                     Email = $"teacher{teacherId:D2}@school.edu",
                     PreferredRoom = preferredRoom,
                     Departments = new[] { dept },
                     TargetLoadBlocks = 18 + (teacherId % 5),
                     IsPartTime = teacherId % 10 == 0,
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

         // Generate classes and streams per grade (reduced courses per grade for feasibility)
         int classId = 1;
         foreach (var grade in grades)
         {
             foreach (var (subject, dept, weeklyBlocks, classSize, coursesPerGrade, equipment, coTeaching) in subjectConfigs)
             {
                 // Grade-level restrictions
                 if (subject == "Physics" && (grade == "9" || grade == "10")) continue;
                 if (subject == "AutoShop" && (grade == "9" || grade == "12")) continue;
                 if (subject == "Drama" && (grade == "11" || grade == "12")) continue;

                 int actualCourses = Math.Min(coursesPerGrade, dept == "Math" || dept == "English" ? 1 : coursesPerGrade);
                 for (int c = 1; c <= actualCourses; c++)
                 {
                     var clsKey = $"{subject}{grade}{c}";
                    var clsStreams = new List<ClassStream>();

                    int streamCount = coTeaching ? 2 : 1;
                    int studentsPerStream = classSize;

                    for (int s = 1; s <= streamCount; s++)
                    {
                        var streamId = $"{clsKey}-S{s:D2}";
                        clsStreams.Add(new ClassStream
                        {
                            Id = streamId,
                            Size = studentsPerStream,
                            ProficiencyLevel = "Mixed",
                            LinkedSubjects = new[] { subject }
                        });
                        streams.Add(clsStreams.Last());
                    }

                    // Assign teachers deterministically
                    if (!teachersByDept.TryGetValue(dept, out var deptTeachersList) || deptTeachersList.Count == 0)
                    {
                        throw new InvalidOperationException($"No teachers found for department '{dept}'.");
                    }

                    List<string> assignedTeacherIds;
                    if (coTeaching)
                    {
                        assignedTeacherIds = deptTeachersList.Take(2).Select(t => t.Id).ToList();
                    }
                    else
                    {
                        if (!nextTeacherIndex.ContainsKey(dept)) nextTeacherIndex[dept] = 0;
                        if (dept == "Special" && nextTeacherIndex[dept] == 0)
                        {
                            nextTeacherIndex[dept] = 2;
                        }
                        int idx = nextTeacherIndex[dept] % deptTeachersList.Count;
                        assignedTeacherIds = new List<string> { deptTeachersList[idx].Id };
                        nextTeacherIndex[dept] = idx + 1;
                    }

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
                        .FirstOrDefault(r => r.EquipmentType == roomEquipment)?.Id ?? "Room01";

                    classes.Add(new Class
                    {
                        Key = clsKey,
                        Name = $"{subject} {grade}.{c}",
                        Department = dept,
                        PreferredRoom = preferredRoom,
                        WeeklyBlocks = weeklyBlocks,
                        Streams = clsStreams,
                        TeacherIds = assignedTeacherIds
                    });
                    classId++;
                }
            }
        }

        return new SchedulerOptions
        {
            Days = SchedulerOptions.MonTueWedThuFri,
            BlocksPerDay = 9,
            Teachers = teachers,
            Classes = classes,
            Streams = streams,
            Rooms = rooms,
            TeacherDepartments = teacherDepartments,
            ScheduleType = BlockScheduleType.Traditional,
            AllowRoomSharing = true,
            SolverTimeLimitSeconds = 120,
            RoomChangePenalty = 3,
            ScheduleSpreadPenalty = 2,
            WeekDistributionPenalty = 1,
            ClassDayClusteringPenalty = 1,
            ClassBlockConsistencyPenalty = 1,
            StreamFragmentationPenalty = 1,
            SharedRoomChangePenalty = 3,
            TargetLoadAdherencePenalty = 2,
            StudentRoomTransitionPenalty = 2,
            MergedBlockConsistencyPenalty = 1,
            FreeTimePenalty = 1,
            CommonPlanningPenalty = 1
        };
    }
}
