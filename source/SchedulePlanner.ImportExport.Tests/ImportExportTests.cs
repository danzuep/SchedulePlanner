using SchedulePlanner.ImportExport.Excel;

namespace SchedulePlanner.ImportExport.Tests
{
    public class ImportExportTests
    {
        [Test]
        public async Task ImportExport_AssemblyLoads()
        {
            var type = typeof(ImportExportService);
            await Assert.That(type).IsNotNull();
        }

        [Test]
        public async Task ExcelReader_Exists()
        {
            var type = typeof(ExcelSchedulerConfigReader);
            await Assert.That(type).IsNotNull();
        }

        [Test]
        public async Task ExcelWriter_Exists()
        {
            var type = typeof(ExcelSchedulerConfigWriter);
            await Assert.That(type).IsNotNull();
        }
    }
}
