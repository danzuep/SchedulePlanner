using System.Text;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;

namespace SchedulePlanner.Core
{
    public interface IScheduleLogger
    {
        void LogResult(ScheduleResult result);
    }

    public sealed class ScheduleLogger : IScheduleLogger
    {
        private readonly ILogger<ScheduleLogger> _logger;

        public ScheduleLogger(ILogger<ScheduleLogger>? logger = null)
        {
            _logger = logger ?? NullLogger<ScheduleLogger>.Instance;
        }

        public void LogResult(ScheduleResult result)
        {
            if (!result.HasSolution)
            {
                _logger.LogWarning(
                    "Solver finished with status {Status}; no timetable was produced.",
                    result.Status);

                _logger.LogInformation("Solver statistics: {Stats}", result.SolverStatistics);
                return;
            }

            _logger.LogInformation(
                "Timetable objective value (room-change penalties): {Objective}",
                result.ObjectiveValue);

            foreach (var teacher in result.TeacherSchedules)
            {
                _logger.LogInformation("Schedule for {Teacher} (ID {TeacherId}):", teacher.TeacherName, teacher.TeacherId);

                foreach (var day in teacher.Days)
                {
                    var builder = new StringBuilder();
                    builder.Append($"{day.Day,-9}: ");

                    foreach (var block in day.Blocks)
                    {
                        if (block.IsFree)
                        {
                            builder.Append("Free ");
                        }
                        else
                        {
                            builder.Append($"{block.ClassKey}({block.Room}) ");
                        }
                    }

                    _logger.LogInformation(builder.ToString());
                }
            }

            foreach (var classSummary in result.Classes)
            {
                _logger.LogInformation(
                    "Class {ClassId} scheduled for {Count}/{Required} blocks.",
                    classSummary.ClassKey,
                    classSummary.ScheduledBlocks,
                    classSummary.RequiredBlocks);
            }

            // Log stream completion rates
            if (result.StreamSchedules != null)
            {
                foreach (var streamSchedule in result.StreamSchedules)
                {
                    var totalBlocks = streamSchedule.Days.Sum(d => d.Blocks.Count(b => !b.IsFree));
                    _logger.LogInformation(
                        "Stream {StreamId} for class {ClassKey} scheduled for {Count} blocks.",
                        streamSchedule.StreamId,
                        streamSchedule.ClassKey,
                        totalBlocks);
                }
            }

            // Log room utilization
            if (result.RoomUtilizations != null)
            {
                foreach (var roomUtil in result.RoomUtilizations)
                {
                    _logger.LogInformation(
                        "Room {RoomId} utilization: {Percent:F2}%.",
                        roomUtil.RoomId,
                        roomUtil.UtilizationPercent);
                }
            }

            foreach (var roomChange in result.RoomChanges)
            {
                _logger.LogInformation(
                    "Penalty: {Teacher} changes from {FromRoom} ({FromClass}) to {ToRoom} ({ToClass}) on {Day} block {Block} -> {NextBlock}.",
                    roomChange.TeacherName,
                    roomChange.FromRoom,
                    roomChange.FromClassKey,
                    roomChange.ToRoom,
                    roomChange.ToClassKey,
                    roomChange.Day,
                    roomChange.FromBlock,
                    roomChange.ToBlock);
            }

            _logger.LogInformation("Solver statistics: {Stats}", result.SolverStatistics);
        }
    }
}
