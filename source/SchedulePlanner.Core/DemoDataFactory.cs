namespace SchedulePlanner.Core;

/// <summary>
/// Configuration object to define school scale and constraints without logic.
/// </summary>
public class DemoConfig
{
    public string[] Grades { get; set; } = Array.Empty<string>();
    public int BlocksPerDay { get; set; } = 7;
    public List<DeptDefinition> Departments { get; set; } = new();
    public List<RoomDefinition> RoomGroups { get; set; } = new();
    public int SolverTimeLimit { get; set; } = 30;
    public bool AllowRoomSharing { get; set; } = true;
}

public record DeptDefinition(string Name, int TeacherCount, List<SubjectDefinition> Subjects);
public record SubjectDefinition(string Name, int WeeklyBlocks, int ClassSize, int CoursesPerGrade, string? Equipment = null, bool CoTeaching = false);
public record RoomDefinition(string Type, string Equipment, int Capacity, int Count, int SetupBuffer = 0);

public static class DemoDataFactory
{
    public static SchedulerOptions CreateDemo(DemoConfig config)
    {
        var rooms = GenerateRooms(config.RoomGroups);
        var teachers = GenerateTeachers(config.Departments, rooms);

        // Flatten teacher-department mapping for the scheduler
        var teacherDepts = teachers.SelectMany(t => t.Departments.Select(d =>
            new TeacherDepartment { TeacherId = t.Id, Department = d })).ToList();

        var (classes, streams) = GenerateClassesAndStreams(config, teachers, rooms);

        var options = new SchedulerOptions
        {
            Days = SchedulerOptions.MonTueWedThuFri,
            BlocksPerDay = config.BlocksPerDay,
            Teachers = teachers,
            Rooms = rooms,
            Classes = classes,
            Streams = streams,
            TeacherDepartments = teacherDepts,
            AllowRoomSharing = config.AllowRoomSharing,
            SolverTimeLimitSeconds = config.SolverTimeLimit,
            RoomChangePenalty = 3,
            ScheduleSpreadPenalty = 2,
            TargetLoadAdherencePenalty = 2
        };

        return options;
    }

    private static List<Room> GenerateRooms(List<RoomDefinition> groups)
    {
        var rooms = new List<Room>();
        foreach (var group in groups)
        {
            for (int i = 1; i <= group.Count; i++)
            {
                rooms.Add(new Room
                {
                    Id = $"{group.Type}{i:D2}",
                    Capacity = group.Capacity,
                    EquipmentType = group.Equipment,
                    SetupTimeBuffer = group.SetupBuffer
                });
            }
        }
        return rooms;
    }

    private static List<Teacher> GenerateTeachers(List<DeptDefinition> depts, List<Room> rooms)
    {
        var teachers = new List<Teacher>();
        int globalId = 1;

        foreach (var dept in depts)
        {
            for (int i = 0; i < dept.TeacherCount; i++)
            {
                teachers.Add(new Teacher
                {
                    Id = $"T{globalId:D2}",
                    FullName = $"Teacher {globalId:D2}",
                    Departments = new[] { dept.Name },
                    PreferredRoom = rooms.FirstOrDefault(r => r.EquipmentType == "Standard")?.Id ?? "Room01",
                    TargetLoadBlocks = 18 + (globalId % 3),
                    MaxConsecutiveBlocks = 4,
                    Certifications = dept.Subjects.Select(s => s.Name).ToArray()
                });
                globalId++;
            }
        }
        return teachers;
    }

    private static (List<Class>, List<ClassStream>) GenerateClassesAndStreams(DemoConfig config, List<Teacher> teachers, List<Room> rooms)
    {
        var classes = new List<Class>();
        var streams = new List<ClassStream>();
        var teacherCounters = new Dictionary<string, int>();

        foreach (var grade in config.Grades)
        {
            foreach (var dept in config.Departments)
            {
                var deptTeachers = teachers.Where(t => t.Departments.Contains(dept.Name)).ToList();

                foreach (var sub in dept.Subjects)
                {
                    for (int c = 1; c <= sub.CoursesPerGrade; c++)
                    {
                        var clsKey = $"{sub.Name}{grade}{c}";
                        var clsStreams = new List<ClassStream> {
                            new ClassStream { Id = $"{clsKey}-S1", Size = sub.ClassSize, LinkedSubjects = new[] { sub.Name } }
                        };

                        // Assign teacher using round-robin logic
                        teacherCounters[dept.Name] = teacherCounters.GetValueOrDefault(dept.Name, 0);
                        var assignedTeacher = deptTeachers[teacherCounters[dept.Name] % deptTeachers.Count];
                        teacherCounters[dept.Name]++;

                        classes.Add(new Class
                        {
                            Key = clsKey,
                            Name = $"{sub.Name} {grade}.{c}",
                            Department = dept.Name,
                            WeeklyBlocks = sub.WeeklyBlocks,
                            PreferredRoom = rooms.FirstOrDefault(r => r.EquipmentType == (sub.Equipment ?? "Standard"))?.Id,
                            TeacherIds = new List<string> { assignedTeacher.Id },
                            Streams = clsStreams
                        });
                        streams.AddRange(clsStreams);
                    }
                }
            }
        }
        return (classes, streams);
    }

    public static SchedulerOptions CreateSmallHighSchoolDemo()
    {
        var config = new DemoConfig
        {
            Grades = ["9", "10"],
            BlocksPerDay = 7,
            Departments = [
                new DeptDefinition("Math", 2, [
                    new SubjectDefinition("Algebra", 4, 25, 1),
                    new SubjectDefinition("Geometry", 4, 25, 1)
                ]),
                new DeptDefinition("Science", 1, [
                    new SubjectDefinition("Biology", 4, 25, 1),
                    new SubjectDefinition("Chemistry", 4, 20, 1)
                ]),
                new DeptDefinition("English", 1, [
                    new SubjectDefinition("English", 4, 25, 1)
                ])
            ],
            RoomGroups = [
                new RoomDefinition("Classroom", "Standard", 30, 3),
                new RoomDefinition("Lab", "Lab", 25, 1)
            ],
            SolverTimeLimit = 30
        };
        return CreateDemo(config);
    }

    public static SchedulerOptions CreateLargeHighSchoolDemo()
    {
        var config = new DemoConfig
        {
            Grades = ["9", "10", "11", "12"],
            BlocksPerDay = 9,
            Departments = [
                new DeptDefinition("Math", 5, [
                    new SubjectDefinition("Algebra", 4, 25, 1),
                    new SubjectDefinition("Geometry", 4, 25, 1),
                    new SubjectDefinition("Calculus", 5, 20, 1),
                    new SubjectDefinition("Statistics", 3, 20, 1)
                ]),
                new DeptDefinition("Science", 5, [
                    new SubjectDefinition("Biology", 4, 25, 1),
                    new SubjectDefinition("Chemistry", 5, 20, 1),
                    new SubjectDefinition("Physics", 5, 20, 1),
                    new SubjectDefinition("EarthScience", 3, 25, 1)
                ]),
                new DeptDefinition("English", 3, [
                    new SubjectDefinition("English", 4, 25, 1),
                    new SubjectDefinition("Literature", 3, 25, 1)
                ]),
                new DeptDefinition("History", 3, [
                    new SubjectDefinition("WorldHistory", 4, 25, 1),
                    new SubjectDefinition("USHistory", 4, 25, 1),
                    new SubjectDefinition("Government", 3, 25, 1)
                ]),
                new DeptDefinition("Arts", 2, [
                    new SubjectDefinition("Art", 3, 20, 1),
                    new SubjectDefinition("Music", 3, 25, 1)
                ])
            ],
            RoomGroups = [
                new RoomDefinition("Classroom", "Standard", 30, 15),
                new RoomDefinition("Lab", "Lab", 25, 5),
                new RoomDefinition("Auditorium", "Auditorium", 100, 1),
                new RoomDefinition("Gym", "Gym", 50, 2)
            ],
            SolverTimeLimit = 300
        };
        return CreateDemo(config);
    }

    public static SchedulerOptions CreateUnsolvableDemo()
    {
        var config = new DemoConfig
        {
            Grades = ["9", "10", "11", "12"],
            BlocksPerDay = 7,
            Departments = [
                new DeptDefinition("Math", 2, [
                    new SubjectDefinition("Algebra", 4, 25, 2),
                    new SubjectDefinition("Geometry", 4, 25, 1),
                    new SubjectDefinition("Calculus", 5, 20, 1),
                    new SubjectDefinition("Statistics", 3, 20, 1),
                    new SubjectDefinition("Trigonometry", 3, 20, 1)
                ]),
                new DeptDefinition("Science", 1, [
                    new SubjectDefinition("Biology", 4, 25, 1),
                    new SubjectDefinition("Chemistry", 5, 20, 1),
                    new SubjectDefinition("Physics", 5, 20, 1),
                    new SubjectDefinition("EarthScience", 3, 25, 1)
                ]),
                new DeptDefinition("English", 1, [
                    new SubjectDefinition("English", 4, 25, 2),
                    new SubjectDefinition("Literature", 3, 25, 1)
                ])
            ],
            RoomGroups = [
                new RoomDefinition("Classroom", "Standard", 30, 1)
            ],
            SolverTimeLimit = 300 // Long time limit so timeout triggers first
        };
        return CreateDemo(config);
    }
}