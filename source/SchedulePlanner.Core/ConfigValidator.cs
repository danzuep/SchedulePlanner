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

            if (config.TeacherDepartments == null || !config.TeacherDepartments.Any())
            {
                throw new InvalidOperationException("At least one department assignment is required.");
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

            return new NormalizedSettings(solverTimeLimitSeconds, roomChangePenalty, scheduleSpreadPenalty);
        }
    }

    public sealed record NormalizedSettings(double SolverTimeLimitSeconds, int RoomChangePenalty, int ScheduleSpreadPenalty);
}
