using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;

namespace SchedulePlanner.Core
{
    public interface IConfigValidator
    {
        NormalizedSettings ValidateAndNormalizeConfig(SchedulerOptions config);
    }

    public sealed class ConfigValidator : IConfigValidator
    {
        private readonly ILogger<ConfigValidator> _logger;

        public ConfigValidator(ILogger<ConfigValidator>? logger = null)
        {
            _logger = logger ?? NullLogger<ConfigValidator>.Instance;
        }

        public NormalizedSettings ValidateAndNormalizeConfig(SchedulerOptions config)
        {
            if (config.Days == null || !config.Days.Any())
            {
                throw new InvalidOperationException("You must specify at least one day in the Scheduler configuration.");
            }

            if (config.BlocksPerDay <= 0)
            {
                throw new InvalidOperationException("BlocksPerDay must be greater than zero.");
            }

            if (config.Classes == null || !config.Classes.Any())
            {
                throw new InvalidOperationException("At least one class must be defined.");
            }

            if (config.Teachers == null || !config.Teachers.Any())
            {
                throw new InvalidOperationException("At least one teacher must be defined.");
            }

            var solverTimeLimitSeconds = config.SolverTimeLimitSeconds > 0
                ? config.SolverTimeLimitSeconds
                : 10.0;

            if (config.SolverTimeLimitSeconds <= 0)
            {
                _logger.LogWarning(
                    "SolverTimeLimitSeconds must be greater than zero; falling back to {DefaultTime} seconds.",
                    solverTimeLimitSeconds);
            }

            var roomChangePenalty = Math.Max(0, config.RoomChangePenalty);

            if (config.RoomChangePenalty < 0)
            {
                _logger.LogWarning("RoomChangePenalty must be non-negative; falling back to zero.");
            }

            var scheduleSpreadPenalty = Math.Max(0, config.ScheduleSpreadPenalty);

            if (config.ScheduleSpreadPenalty < 0)
            {
                _logger.LogWarning("ScheduleSpreadPenalty must be non-negative; falling back to zero.");
            }

            var weekDistributionPenalty = Math.Max(0, config.WeekDistributionPenalty);

            if (config.WeekDistributionPenalty < 0)
            {
                _logger.LogWarning("WeekDistributionPenalty must be non-negative; falling back to zero.");
            }

            var classDayClusteringPenalty = Math.Max(0, config.ClassDayClusteringPenalty);

            if (config.ClassDayClusteringPenalty < 0)
            {
                _logger.LogWarning("ClassDayClusteringPenalty must be non-negative; falling back to zero.");
            }

            var classBlockConsistencyPenalty = Math.Max(0, config.ClassBlockConsistencyPenalty);

            if (config.ClassBlockConsistencyPenalty < 0)
            {
                _logger.LogWarning("ClassBlockConsistencyPenalty must be non-negative; falling back to zero.");
            }

            var streamFragmentationPenalty = Math.Max(0, config.StreamFragmentationPenalty);

            if (config.StreamFragmentationPenalty < 0)
            {
                _logger.LogWarning("StreamFragmentationPenalty must be non-negative; falling back to zero.");
            }

            var sharedRoomChangePenalty = Math.Max(0, config.SharedRoomChangePenalty);

            if (config.SharedRoomChangePenalty < 0)
            {
                _logger.LogWarning("SharedRoomChangePenalty must be non-negative; falling back to zero.");
            }

            var targetLoadAdherencePenalty = Math.Max(0, config.TargetLoadAdherencePenalty);

            if (config.TargetLoadAdherencePenalty < 0)
            {
                _logger.LogWarning("TargetLoadAdherencePenalty must be non-negative; falling back to zero.");
            }

            var studentRoomTransitionPenalty = Math.Max(0, config.StudentRoomTransitionPenalty);

            if (config.StudentRoomTransitionPenalty < 0)
            {
                _logger.LogWarning("StudentRoomTransitionPenalty must be non-negative; falling back to zero.");
            }

            var freeTimePenalty = Math.Max(0, config.FreeTimePenalty);

            if (config.FreeTimePenalty < 0)
            {
                _logger.LogWarning("FreeTimePenalty must be non-negative; falling back to zero.");
            }

            var mergedBlockConsistencyPenalty = Math.Max(0, config.MergedBlockConsistencyPenalty);

            if (config.MergedBlockConsistencyPenalty < 0)
            {
                _logger.LogWarning("MergedBlockConsistencyPenalty must be non-negative; falling back to zero.");
            }

            var commonPlanningPenalty = Math.Max(0, config.CommonPlanningPenalty);

            if (config.CommonPlanningPenalty < 0)
            {
                _logger.LogWarning("CommonPlanningPenalty must be non-negative; falling back to zero.");
            }

            // Additional validations for K-12 features
            ValidateStreams(config);
            ValidateRooms(config);
            ValidateMergedBlocks(config);
            ValidateDayConfigs(config);

            return new NormalizedSettings(solverTimeLimitSeconds, roomChangePenalty, scheduleSpreadPenalty, weekDistributionPenalty, classDayClusteringPenalty, classBlockConsistencyPenalty, streamFragmentationPenalty, sharedRoomChangePenalty, targetLoadAdherencePenalty, studentRoomTransitionPenalty, mergedBlockConsistencyPenalty, freeTimePenalty, commonPlanningPenalty);
        }

        private void ValidateStreams(SchedulerOptions config)
        {
            if (config.Streams == null) return;

            var streamIds = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
            foreach (var stream in config.Streams)
            {
                if (string.IsNullOrWhiteSpace(stream.Id))
                {
                    throw new InvalidOperationException("Stream must have a valid Id.");
                }
                if (!streamIds.Add(stream.Id))
                {
                    throw new InvalidOperationException($"Duplicate stream Id: {stream.Id}");
                }
                if (stream.Size <= 0)
                {
                    throw new InvalidOperationException($"Stream {stream.Id} must have positive size.");
                }
            }

            // Check class streams
            if (config.Classes != null)
            {
                foreach (var cls in config.Classes)
                {
                    if (cls.Streams != null)
                    {
                        foreach (var stream in cls.Streams)
                        {
                            if (!config.Streams.Any(s => s.Id == stream.Id))
                            {
                                throw new InvalidOperationException($"Stream {stream.Id} in class {cls.Key} not found in global streams.");
                            }
                        }
                    }
                }
            }
        }

        private void ValidateRooms(SchedulerOptions config)
        {
            if (config.Rooms == null) return;

            var roomIds = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
            foreach (var room in config.Rooms)
            {
                if (string.IsNullOrWhiteSpace(room.Id))
                {
                    throw new InvalidOperationException("Room must have a valid Id.");
                }
                if (!roomIds.Add(room.Id))
                {
                    throw new InvalidOperationException($"Duplicate room Id: {room.Id}");
                }
                if (room.Capacity <= 0)
                {
                    throw new InvalidOperationException($"Room {room.Id} must have positive capacity.");
                }
                if (room.SetupTimeBuffer < 0)
                {
                    throw new InvalidOperationException($"Room {room.Id} must have non-negative setup time buffer.");
                }
            }
        }

        private void ValidateMergedBlocks(SchedulerOptions config)
        {
            if (config.MergedBlocks == null) return;

            foreach (var merged in config.MergedBlocks)
            {
                if (merged.BlockIndices == null || merged.BlockIndices.Count < 2)
                {
                    throw new InvalidOperationException("Merged block must have at least two block indices.");
                }
                var indices = merged.BlockIndices.ToList();
                indices.Sort();
                for (int i = 1; i < indices.Count; ++i)
                {
                    if (indices[i] == indices[i - 1])
                    {
                        throw new InvalidOperationException("Merged block contains duplicate indices.");
                    }
                    if (indices[i] != indices[i - 1] + 1)
                    {
                        throw new InvalidOperationException("Merged block indices must be consecutive.");
                    }
                }
                if (indices[0] < 0 || indices[^1] >= config.BlocksPerDay)
                {
                    throw new InvalidOperationException("Merged block indices out of range.");
                }
            }
        }

        private void ValidateDayConfigs(SchedulerOptions config)
        {
            if (config.DayConfigs == null || !config.DayConfigs.Any()) return;

            var daySet = new HashSet<DayOfWeek>(config.Days);
            var configDays = new HashSet<DayOfWeek>();

            foreach (var dc in config.DayConfigs)
            {
                if (!daySet.Contains(dc.Day))
                {
                    throw new InvalidOperationException($"DayConfig for {dc.Day} is not in the scheduling days.");
                }
                if (configDays.Contains(dc.Day))
                {
                    throw new InvalidOperationException($"Duplicate DayConfig for {dc.Day}.");
                }
                configDays.Add(dc.Day);

                if (dc.BlocksPerDay <= 0)
                {
                    throw new InvalidOperationException($"BlocksPerDay for {dc.Day} must be positive.");
                }

                // Validate MergedBlocks for this day
                if (dc.MergedBlocks != null)
                {
                    foreach (var merged in dc.MergedBlocks)
                    {
                        if (merged.BlockIndices == null || merged.BlockIndices.Count < 2)
                        {
                            throw new InvalidOperationException("Merged block must have at least two block indices.");
                        }
                        var indices = merged.BlockIndices.ToList();
                        indices.Sort();
                        for (int i = 1; i < indices.Count; ++i)
                        {
                            if (indices[i] == indices[i - 1])
                            {
                                throw new InvalidOperationException("Merged block contains duplicate indices.");
                            }
                            if (indices[i] != indices[i - 1] + 1)
                            {
                                throw new InvalidOperationException("Merged block indices must be consecutive.");
                            }
                        }
                        if (indices[0] < 0 || indices[^1] >= dc.BlocksPerDay)
                        {
                            throw new InvalidOperationException($"Merged block indices for {dc.Day} out of range.");
                        }
                    }
                }
            }

            if (configDays.Count != daySet.Count)
            {
                throw new InvalidOperationException("Not all scheduling days have DayConfigs.");
            }
        }
    }

    public sealed record NormalizedSettings(double SolverTimeLimitSeconds, int RoomChangePenalty, int ScheduleSpreadPenalty, int WeekDistributionPenalty, int ClassDayClusteringPenalty, int ClassBlockConsistencyPenalty, int StreamFragmentationPenalty, int SharedRoomChangePenalty, int TargetLoadAdherencePenalty, int StudentRoomTransitionPenalty, int MergedBlockConsistencyPenalty, int FreeTimePenalty, int CommonPlanningPenalty);
}
