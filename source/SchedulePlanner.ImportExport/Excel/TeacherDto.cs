using SchedulePlanner.Core;

namespace SchedulePlanner.ImportExport.Excel
{
    internal class TeacherDto
    {
        public TeacherDto(Teacher t)
        {
            Id = t.Id;
            FullName = t.FullName;
            PreferredRoom = t.PreferredRoom;
            TargetLoadBlocks = t.TargetLoadBlocks;
            Departments = string.Join(",", t.Departments ?? Array.Empty<string>());
        }

        public string Id { get; set; }
        public string FullName { get; set; }
        public string PreferredRoom { get; set; }
        public int TargetLoadBlocks { get; set; }
        public string Departments { get; set; }
    }
}