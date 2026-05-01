namespace SchedulePlanner.Core
{
    public interface IClassAssignmentBuilder
    {
        IReadOnlyList<ClassAssignment> BuildClassAssignments(SchedulerOptions config);
        IReadOnlyDictionary<string, TeacherGroup> BuildTeacherGroups(IReadOnlyList<ClassAssignment> classAssignments);
        IReadOnlyDictionary<string, IReadOnlyList<ClassAssignment>> BuildRoomGroups(IReadOnlyList<ClassAssignment> classAssignments);
    }

    public sealed class ClassAssignmentBuilder : IClassAssignmentBuilder
    {
    public IReadOnlyList<ClassAssignment> BuildClassAssignments(SchedulerOptions config)
    {
        var comparer = StringComparer.OrdinalIgnoreCase;

        var teachersById = config.Teachers
            .ToDictionary(t => t.Id, t => t, comparer);

        var assignmentsByDepartment = new Dictionary<string, List<string>>(StringComparer.OrdinalIgnoreCase);

        // From teacher Departments
        foreach (var teacher in config.Teachers)
        {
            if (teacher.Departments == null) continue;
            foreach (var dept in teacher.Departments)
            {
                if (string.IsNullOrWhiteSpace(dept)) continue;
                if (!assignmentsByDepartment.TryGetValue(dept, out var list))
                {
                    list = new List<string>();
                    assignmentsByDepartment[dept] = list;
                }
                list.Add(teacher.Id);
            }
        }

        // From explicit TeacherDepartments mapping
        if (config.TeacherDepartments != null)
        {
            foreach (var td in config.TeacherDepartments)
            {
                if (string.IsNullOrWhiteSpace(td.Department)) continue;
                if (!assignmentsByDepartment.TryGetValue(td.Department, out var list))
                {
                    list = new List<string>();
                    assignmentsByDepartment[td.Department] = list;
                }
                list.Add(td.TeacherId);
            }
        }

        // Ensure distinct teacher IDs per department
        foreach (var key in assignmentsByDepartment.Keys.ToList())
        {
            assignmentsByDepartment[key] = assignmentsByDepartment[key].Distinct(comparer).ToList();
        }

        var results = new List<ClassAssignment>(config.Classes.Count);

        for (var index = 0; index < config.Classes.Count; ++index)
        {
            var cls = config.Classes[index];

            if (string.IsNullOrWhiteSpace(cls.Key))
            {
                throw new InvalidOperationException($"Class at index {index} must define a Key.");
            }

            var teacherIds = cls.TeacherIds.Any() ? cls.TeacherIds : null;
            if (teacherIds == null)
            {
                if (string.IsNullOrWhiteSpace(cls.Department))
                {
                    throw new InvalidOperationException($"Class {cls.Key} must specify a department.");
                }

                if (!assignmentsByDepartment.TryGetValue(cls.Department, out var candidates) || candidates.Count == 0)
                {
                    throw new InvalidOperationException(
                        $"No teacher assignment exists for department '{cls.Department}' required by class '{cls.Key}'.");
                }

                // For classes without streams (single-teacher), select exactly one teacher.
                // For streamed classes (co-teaching allowed), keep all candidates.
                if (cls.Streams.Count == 0)
                {
                    teacherIds = new List<string> { candidates.First() };
                }
                else
                {
                    teacherIds = candidates.ToList();
                }
            }

            // Validate: there must be exactly one teacher ID for single-teacher classes; multiple only if explicitly allowed (co-teaching)
            if (teacherIds.Count > 1 && cls.Streams.Count == 0)
            {
                throw new InvalidOperationException(
                    $"Multiple teachers assigned to class '{cls.Key}' without co-teaching (streams) is not allowed.");
            }

            var teachers = new List<Teacher>();
            foreach (var teacherId in teacherIds)
            {
                if (!teachersById.TryGetValue(teacherId, out var teacher))
                {
                    throw new InvalidOperationException($"Class {cls.Key} references unknown teacher '{teacherId}'.");
                }
                teachers.Add(teacher);
            }

            var room = ResolveRoom(cls, teachers.First(), config); // Use first teacher for room resolution
            if (string.IsNullOrWhiteSpace(room))
            {
                throw new InvalidOperationException(
                    $"Unable to determine a room for class {cls.Key} taught by {string.Join(", ", teachers.Select(t => t.FullName))}.");
            }

            // For classes without streams, create a single assignment with unique sequential index
            if (cls.Streams.Count == 0)
            {
                var assignmentIndex = results.Count;
                results.Add(new ClassAssignment(cls, teachers, assignmentIndex, room, null));
            }
            else
            {
                // For streamed classes, create an assignment for each stream
                foreach (var stream in cls.Streams)
                {
                    var assignmentIndex = results.Count;
                    results.Add(new ClassAssignment(cls, teachers, assignmentIndex, room, stream));
                }
            }
        }

        return results;
    }

        public IReadOnlyDictionary<string, TeacherGroup> BuildTeacherGroups(IReadOnlyList<ClassAssignment> classAssignments)
        {
            var teacherGroups = new Dictionary<string, List<ClassAssignment>>(StringComparer.OrdinalIgnoreCase);

            foreach (var assignment in classAssignments)
            {
                foreach (var teacher in assignment.Teachers)
                {
                    if (!teacherGroups.TryGetValue(teacher.Id, out var list))
                    {
                        list = new List<ClassAssignment>();
                        teacherGroups[teacher.Id] = list;
                    }
                    list.Add(assignment);
                }
            }

            return teacherGroups.ToDictionary(
                kvp => kvp.Key,
                kvp => new TeacherGroup(kvp.Value.First().Teachers.First(t => t.Id == kvp.Key), kvp.Value),
                StringComparer.OrdinalIgnoreCase);
        }

        public IReadOnlyDictionary<string, IReadOnlyList<ClassAssignment>> BuildRoomGroups(
            IReadOnlyList<ClassAssignment> classAssignments)
        {
            return classAssignments
                .GroupBy(entry => entry.Room, StringComparer.OrdinalIgnoreCase)
                .ToDictionary(
                    g => g.Key,
                    g => (IReadOnlyList<ClassAssignment>)g.ToList(),
                    StringComparer.OrdinalIgnoreCase);
        }

        private static string ResolveRoom(Class cls, Teacher teacher, SchedulerOptions config)
        {
            // Priority: 1) teacher.PreferredRoom, 2) cls.PreferredRoom, 3) any suitable room from config, 4) default based on class key
            // Determine required capacity: if class has streams, use the largest stream size; otherwise no requirement (0).
            var required = cls.Streams.Count > 0 ? cls.Streams.Max(s => s.Size) : 0;

            bool RoomSuitable(string roomId)
            {
                if (required == 0) return true;
                var capacity = GetRoomCapacity(config, roomId);
                return required <= capacity;
            }

            // Try teacher's preferred room
            if (!string.IsNullOrWhiteSpace(teacher.PreferredRoom) && RoomSuitable(teacher.PreferredRoom))
            {
                return teacher.PreferredRoom;
            }

            // Try class's preferred room
            if (!string.IsNullOrWhiteSpace(cls.PreferredRoom) && RoomSuitable(cls.PreferredRoom))
            {
                return cls.PreferredRoom;
            }

            // Try any room in config that satisfies capacity
            if (config.Rooms != null)
            {
                foreach (var room in config.Rooms)
                {
                    if (RoomSuitable(room.Id))
                    {
                        return room.Id;
                    }
                }
            }

            // No suitable room found
            throw new InvalidOperationException(
                $"Unable to determine a suitable room for class {cls.Key} taught by {teacher.FullName}. " +
                $"Ensure teacher or class has a preferred room, or define rooms in the configuration.");
        }

        private static int GetRoomCapacity(SchedulerOptions config, string roomId)
        {
            return config.Rooms.FirstOrDefault(r => r.Id == roomId)?.Capacity ?? int.MaxValue;
        }
    }

    public sealed record ClassAssignment(Class Config, IReadOnlyList<Teacher> Teachers, int Index, string Room, ClassStream? ClassStream)
    {
        public Teacher Teacher => Teachers.FirstOrDefault();
    }

    public sealed record TeacherGroup(Teacher Teacher, IReadOnlyList<ClassAssignment> Classes);
}
