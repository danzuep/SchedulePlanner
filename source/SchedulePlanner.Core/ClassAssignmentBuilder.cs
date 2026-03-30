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

            var assignmentsByDepartment = config.TeacherDepartments
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

                if (string.IsNullOrWhiteSpace(cls.Department))
                {
                    throw new InvalidOperationException($"Class {cls.Key} must specify a department.");
                }

                if (!assignmentsByDepartment.TryGetValue(cls.Department, out var teacherIds) || teacherIds.Count == 0)
                {
                    throw new InvalidOperationException(
                        $"No teacher assignment exists for department '{cls.Department}' required by class '{cls.Key}'.");
                }

                if (teacherIds.Count > 1)
                {
                    throw new InvalidOperationException(
                        $"Multiple teachers are assigned to department '{cls.Department}', so class '{cls.Key}' cannot resolve its teacher.");
                }

                var teacherId = teacherIds[0];
                if (!teachersById.TryGetValue(teacherId, out var teacher))
                {
                    throw new InvalidOperationException($"Class {cls.Key} references unknown teacher '{teacherId}'.");
                }

                var room = ResolveRoom(cls, teacher);
                if (string.IsNullOrWhiteSpace(room))
                {
                    throw new InvalidOperationException(
                        $"Unable to determine a room for class {cls.Key} taught by {teacher.FullName}.");
                }

                results.Add(new ClassAssignment(cls, teacher, index, room));
            }

            return results;
        }

        public IReadOnlyDictionary<string, TeacherGroup> BuildTeacherGroups(IReadOnlyList<ClassAssignment> classAssignments)
        {
            return classAssignments
                .GroupBy(entry => entry.Teacher.Id, StringComparer.OrdinalIgnoreCase)
                .ToDictionary(
                    g => g.Key,
                    g => new TeacherGroup(g.First().Teacher, g.ToList()),
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

        private static string ResolveRoom(Class cls, Teacher teacher)
        {
            if (!string.IsNullOrWhiteSpace(teacher.PreferredRoom))
            {
                return teacher.PreferredRoom;
            }

            if (!string.IsNullOrWhiteSpace(cls.PreferredRoom))
            {
                return cls.PreferredRoom;
            }

            return string.Empty;
        }
    }

    public sealed record ClassAssignment(Class Config, Teacher Teacher, int Index, string Room);

    public sealed record TeacherGroup(Teacher Teacher, IReadOnlyList<ClassAssignment> Classes);
}
