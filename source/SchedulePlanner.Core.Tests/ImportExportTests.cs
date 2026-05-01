namespace SchedulePlanner.Core.Tests
{
    public class ImportExportTests
    {
        [Test]
        public async Task ImportExport_AssemblyLoads()
        {
            var type = typeof(SchedulePlanner.ImportExport.Excel.ImportExportService);
            await Assert.That(type).IsNotNull();
        }

        [Test]
        public async Task ExcelReader_Exists()
        {
            var type = typeof(SchedulePlanner.ImportExport.Excel.ExcelSchedulerConfigReader);
            await Assert.That(type).IsNotNull();
        }

        [Test]
        public async Task ExcelWriter_Exists()
        {
            var type = typeof(SchedulePlanner.ImportExport.Excel.ExcelSchedulerConfigWriter);
            await Assert.That(type).IsNotNull();
        }
    }
}
