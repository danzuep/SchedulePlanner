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

        var assignmentsByDepartment = config.Teachers
            .SelectMany(t => t.Departments.Select(d => new { Department = d, TeacherId = t.Id }))
            .Where(a => !string.IsNullOrWhiteSpace(a.Department))
            .GroupBy(a => a.Department, comparer)
            .ToDictionary(
                g => g.Key,
                g => g.Select(a => a.TeacherId)
                    .Where(id => !string.IsNullOrWhiteSpace(id))
                    .Distinct(comparer)
                    .ToList(),
                comparer);

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

                if (!assignmentsByDepartment.TryGetValue(cls.Department, out teacherIds) || teacherIds.Count == 0)
                {
                    throw new InvalidOperationException(
                        $"No teacher assignment exists for department '{cls.Department}' required by class '{cls.Key}'.");
                }
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

            // For classes without streams, create a single assignment
            if (cls.Streams.Count == 0)
            {
                results.Add(new ClassAssignment(cls, teachers, index, room, null));
            }
            else
            {
                // For streamed classes, create an assignment for each stream
                foreach (var stream in cls.Streams)
                {
                    results.Add(new ClassAssignment(cls, teachers, index, room, stream));
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
            var candidate = !string.IsNullOrWhiteSpace(cls.PreferredRoom) ? cls.PreferredRoom :
                            !string.IsNullOrWhiteSpace(teacher.PreferredRoom) ? teacher.PreferredRoom :
                            string.Empty;

            if (string.IsNullOrWhiteSpace(candidate)) return string.Empty;

            var capacity = GetRoomCapacity(config, candidate);
            var required = cls.Streams.Count > 0 ? cls.Streams.Sum(s => s.Size) : 30; // default

            if (required > capacity) return string.Empty;

            return candidate;
        }

        private static int GetRoomCapacity(SchedulerOptions config, string roomId)
        {
            return config.Rooms.FirstOrDefault(r => r.Id == roomId)?.Capacity ?? int.MaxValue;
        }
    }

    public sealed record ClassAssignment(Class Config, IReadOnlyList<Teacher> Teachers, int Index, string Room, ClassStream? Stream);

    public sealed record TeacherGroup(Teacher Teacher, IReadOnlyList<ClassAssignment> Classes);
}
