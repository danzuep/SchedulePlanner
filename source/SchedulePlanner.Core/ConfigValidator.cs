using FluentValidation;
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
        private readonly IValidator<SchedulerOptions> _fluentValidator;

        public ConfigValidator(
            ILogger<ConfigValidator>? logger = null,
            IValidator<SchedulerOptions>? fluentValidator = null)
        {
            _logger = logger ?? NullLogger<ConfigValidator>.Instance;
            _fluentValidator = fluentValidator ?? new Validation.SchedulerOptionsValidator();
        }

        public NormalizedSettings ValidateAndNormalizeConfig(SchedulerOptions config)
        {
            // FluentValidation for business rules - gives clear, structured error messages
            var validationResult = _fluentValidator.Validate(config);
            if (!validationResult.IsValid)
            {
                var errorMessages = string.Join("; ", validationResult.Errors.Select(e => e.ErrorMessage));
                throw new InvalidOperationException($"Configuration validation failed: {errorMessages}");
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
                _logger.LogWarning("RoomChangePenalty must be non-negative; falling back to zero.");

            var scheduleSpreadPenalty = Math.Max(0, config.ScheduleSpreadPenalty);
            if (config.ScheduleSpreadPenalty < 0)
                _logger.LogWarning("ScheduleSpreadPenalty must be non-negative; falling back to zero.");

            var weekDistributionPenalty = Math.Max(0, config.WeekDistributionPenalty);
            if (config.WeekDistributionPenalty < 0)
                _logger.LogWarning("WeekDistributionPenalty must be non-negative; falling back to zero.");

            var classDayClusteringPenalty = Math.Max(0, config.ClassDayClusteringPenalty);
            if (config.ClassDayClusteringPenalty < 0)
                _logger.LogWarning("ClassDayClusteringPenalty must be non-negative; falling back to zero.");

            var classBlockConsistencyPenalty = Math.Max(0, config.ClassBlockConsistencyPenalty);
            if (config.ClassBlockConsistencyPenalty < 0)
                _logger.LogWarning("ClassBlockConsistencyPenalty must be non-negative; falling back to zero.");

            var streamFragmentationPenalty = Math.Max(0, config.StreamFragmentationPenalty);
            if (config.StreamFragmentationPenalty < 0)
                _logger.LogWarning("StreamFragmentationPenalty must be non-negative; falling back to zero.");

            var sharedRoomChangePenalty = Math.Max(0, config.SharedRoomChangePenalty);
            if (config.SharedRoomChangePenalty < 0)
                _logger.LogWarning("SharedRoomChangePenalty must be non-negative; falling back to zero.");

            var targetLoadAdherencePenalty = Math.Max(0, config.TargetLoadAdherencePenalty);
            if (config.TargetLoadAdherencePenalty < 0)
                _logger.LogWarning("TargetLoadAdherencePenalty must be non-negative; falling back to zero.");

            var studentRoomTransitionPenalty = Math.Max(0, config.StudentRoomTransitionPenalty);
            if (config.StudentRoomTransitionPenalty < 0)
                _logger.LogWarning("StudentRoomTransitionPenalty must be non-negative; falling back to zero.");

            var freeTimePenalty = Math.Max(0, config.FreeTimePenalty);
            if (config.FreeTimePenalty < 0)
                _logger.LogWarning("FreeTimePenalty must be non-negative; falling back to zero.");

            var mergedBlockConsistencyPenalty = Math.Max(0, config.MergedBlockConsistencyPenalty);
            if (config.MergedBlockConsistencyPenalty < 0)
                _logger.LogWarning("MergedBlockConsistencyPenalty must be non-negative; falling back to zero.");

            var commonPlanningPenalty = Math.Max(0, config.CommonPlanningPenalty);
            if (config.CommonPlanningPenalty < 0)
                _logger.LogWarning("CommonPlanningPenalty must be non-negative; falling back to zero.");

            return new NormalizedSettings(
                solverTimeLimitSeconds,
                roomChangePenalty,
                scheduleSpreadPenalty,
                weekDistributionPenalty,
                classDayClusteringPenalty,
                classBlockConsistencyPenalty,
                streamFragmentationPenalty,
                sharedRoomChangePenalty,
                targetLoadAdherencePenalty,
                studentRoomTransitionPenalty,
                mergedBlockConsistencyPenalty,
                freeTimePenalty,
                commonPlanningPenalty);
        }
    }

    public sealed record NormalizedSettings(
        double SolverTimeLimitSeconds,
        int RoomChangePenalty,
        int ScheduleSpreadPenalty,
        int WeekDistributionPenalty,
        int ClassDayClusteringPenalty,
        int ClassBlockConsistencyPenalty,
        int StreamFragmentationPenalty,
        int SharedRoomChangePenalty,
        int TargetLoadAdherencePenalty,
        int StudentRoomTransitionPenalty,
        int MergedBlockConsistencyPenalty,
        int FreeTimePenalty,
        int CommonPlanningPenalty);
}
