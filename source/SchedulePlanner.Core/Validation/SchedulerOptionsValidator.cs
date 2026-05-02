using FluentValidation;
using FluentValidation.Results;
using System.Collections;

namespace SchedulePlanner.Core.Validation;

public sealed class SchedulerOptionsValidator : AbstractValidator<SchedulerOptions>
{
    public SchedulerOptionsValidator()
    {
        RuleFor(x => x.Days)
            .NotEmpty().WithMessage("You must specify at least one day in the Scheduler configuration.");

        RuleFor(x => x.BlocksPerDay)
            .GreaterThan(0).WithMessage("BlocksPerDay must be greater than zero.");

        RuleFor(x => x.Classes)
            .NotEmpty().WithMessage("At least one class must be defined.");

        RuleFor(x => x.Teachers)
            .NotEmpty().WithMessage("At least one teacher must be defined.");

        RuleFor(x => x.RoomChangePenalty).GreaterThanOrEqualTo(0).WithMessage("RoomChangePenalty must be non-negative.");
        RuleFor(x => x.ScheduleSpreadPenalty).GreaterThanOrEqualTo(0).WithMessage("ScheduleSpreadPenalty must be non-negative.");
        RuleFor(x => x.WeekDistributionPenalty).GreaterThanOrEqualTo(0).WithMessage("WeekDistributionPenalty must be non-negative.");
        RuleFor(x => x.ClassDayClusteringPenalty).GreaterThanOrEqualTo(0).WithMessage("ClassDayClusteringPenalty must be non-negative.");
        RuleFor(x => x.ClassBlockConsistencyPenalty).GreaterThanOrEqualTo(0).WithMessage("ClassBlockConsistencyPenalty must be non-negative.");
        RuleFor(x => x.StreamFragmentationPenalty).GreaterThanOrEqualTo(0).WithMessage("StreamFragmentationPenalty must be non-negative.");
        RuleFor(x => x.SharedRoomChangePenalty).GreaterThanOrEqualTo(0).WithMessage("SharedRoomChangePenalty must be non-negative.");
        RuleFor(x => x.TargetLoadAdherencePenalty).GreaterThanOrEqualTo(0).WithMessage("TargetLoadAdherencePenalty must be non-negative.");
        RuleFor(x => x.StudentRoomTransitionPenalty).GreaterThanOrEqualTo(0).WithMessage("StudentRoomTransitionPenalty must be non-negative.");
        RuleFor(x => x.FreeTimePenalty).GreaterThanOrEqualTo(0).WithMessage("FreeTimePenalty must be non-negative.");
        RuleFor(x => x.MergedBlockConsistencyPenalty).GreaterThanOrEqualTo(0).WithMessage("MergedBlockConsistencyPenalty must be non-negative.");
        RuleFor(x => x.CommonPlanningPenalty).GreaterThanOrEqualTo(0).WithMessage("CommonPlanningPenalty must be non-negative.");

        RuleFor(x => x.Streams).NotNull();
        RuleForEach(x => x.Streams).SetValidator(new ClassStreamValidator());

        RuleFor(x => x.Classes)
            .Must(x => x == null || x.All(c => c != null))
            .WithMessage("Classes collection contains null entries.");

        RuleForEach(x => x.Classes).SetValidator(new ClassValidator());

        RuleFor(x => x.Rooms)
            .Must(x => x == null || x.All(r => r != null))
            .WithMessage("Rooms collection contains null entries.");

        RuleForEach(x => x.Rooms).SetValidator(new RoomValidator());

        RuleForEach(x => x.MergedBlocks).SetValidator(new MergedBlockValidator());

        RuleForEach(x => x.DayConfigs).SetValidator(new DayConfigValidator());

        RuleFor(x => x.TeacherDepartments)
            .Must(x => x == null || x.All(td => td != null))
            .WithMessage("TeacherDepartments collection contains null entries.");

        RuleForEach(x => x.TeacherDepartments).SetValidator(new TeacherDepartmentValidator());

        RuleForEach(x => x.PreAssignedSlots).SetValidator(new PreAssignedSlotValidator());
    }

    public override ValidationResult Validate(ValidationContext<SchedulerOptions> context)
    {
        var result = base.Validate(context);
        if (!result.IsValid) return result;

        var options = context.InstanceToValidate;

        // Custom cross-property validations that the rule-based system can't handle cleanly
        var customErrors = new List<ValidationFailure>();

        customErrors.AddRange(ValidateStreams(options));
        customErrors.AddRange(ValidateRooms(options));
        customErrors.AddRange(ValidateMergedBlocks(options));
        customErrors.AddRange(ValidateDayConfigs(options));
        customErrors.AddRange(ValidateTeacherDepartments(options));

        if (customErrors.Any())
        {
            foreach (var err in customErrors) result.Errors.Add(err);
        }

        return result;
    }

    private List<ValidationFailure> ValidateStreams(SchedulerOptions options)
    {
        var errors = new List<ValidationFailure>();
        if (options.Streams == null) return errors;

        var streamIds = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var stream in options.Streams)
        {
            if (string.IsNullOrWhiteSpace(stream.Id))
                errors.Add(new ValidationFailure(nameof(SchedulerOptions.Streams), "Stream must have a valid Id."));
            else if (!streamIds.Add(stream.Id!))
                errors.Add(new ValidationFailure(nameof(SchedulerOptions.Streams), $"Duplicate stream Id: {stream.Id}."));
            else if (stream.Size <= 0)
                errors.Add(new ValidationFailure(nameof(SchedulerOptions.Streams), $"Stream {stream.Id} must have positive size."));
        }

        if (options.Classes != null)
        {
            foreach (var cls in options.Classes)
            {
                if (cls.Streams != null)
                {
                    foreach (var stream in cls.Streams)
                    {
                        if (options.Streams.All(s => s.Id != stream.Id))
                            errors.Add(new ValidationFailure(nameof(SchedulerOptions.Classes), $"Stream {stream.Id} in class {cls.Key} not found in global streams."));
                    }
                }
            }
        }
        return errors;
    }

    private List<ValidationFailure> ValidateRooms(SchedulerOptions options)
    {
        var errors = new List<ValidationFailure>();
        if (options.Rooms == null) return errors;

        var roomIds = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var room in options.Rooms)
        {
            if (string.IsNullOrWhiteSpace(room.Id))
                errors.Add(new ValidationFailure(nameof(SchedulerOptions.Rooms), "Room must have a valid Id."));
            else if (!roomIds.Add(room.Id!))
                errors.Add(new ValidationFailure(nameof(SchedulerOptions.Rooms), $"Duplicate room Id: {room.Id}."));
            else if (room.Capacity <= 0)
                errors.Add(new ValidationFailure(nameof(SchedulerOptions.Rooms), $"Room {room.Id} must have positive capacity."));
            else if (room.SetupTimeBuffer < 0)
                errors.Add(new ValidationFailure(nameof(SchedulerOptions.Rooms), $"Room {room.Id} must have non-negative setup time buffer."));
        }
        return errors;
    }

    private List<ValidationFailure> ValidateMergedBlocks(SchedulerOptions options)
    {
        var errors = new List<ValidationFailure>();
        if (options.MergedBlocks == null) return errors;

        foreach (var merged in options.MergedBlocks)
        {
            if (merged.BlockIndices == null || merged.BlockIndices.Count < 2)
            {
                errors.Add(new ValidationFailure(nameof(SchedulerOptions.MergedBlocks), "Merged block must have at least two block indices."));
                continue;
            }
            var indices = merged.BlockIndices.ToList();
            indices.Sort();
            for (int i = 1; i < indices.Count; ++i)
            {
                if (indices[i] == indices[i - 1])
                {
                    errors.Add(new ValidationFailure(nameof(SchedulerOptions.MergedBlocks), "Merged block contains duplicate indices."));
                    break;
                }
                if (indices[i] != indices[i - 1] + 1)
                {
                    errors.Add(new ValidationFailure(nameof(SchedulerOptions.MergedBlocks), "Merged block indices must be consecutive."));
                    break;
                }
            }
            if (indices[0] < 0 || indices[^1] >= options.BlocksPerDay)
                errors.Add(new ValidationFailure(nameof(SchedulerOptions.MergedBlocks), "Merged block indices out of range."));
        }
        return errors;
    }

    private List<ValidationFailure> ValidateDayConfigs(SchedulerOptions options)
    {
        var errors = new List<ValidationFailure>();
        if (options.DayConfigs == null || !options.DayConfigs.Any()) return errors;

        var daySet = new HashSet<DayOfWeek>(options.Days);
        var configDays = new HashSet<DayOfWeek>();

        foreach (var dc in options.DayConfigs)
        {
            if (!daySet.Contains(dc.Day))
                errors.Add(new ValidationFailure(nameof(SchedulerOptions.DayConfigs), $"DayConfig for {dc.Day} is not in the scheduling days."));
            
            if (configDays.Contains(dc.Day))
                errors.Add(new ValidationFailure(nameof(SchedulerOptions.DayConfigs), $"Duplicate DayConfig for {dc.Day}."));
            configDays.Add(dc.Day);

            if (dc.BlocksPerDay <= 0)
                errors.Add(new ValidationFailure(nameof(SchedulerOptions.DayConfigs), $"BlocksPerDay for {dc.Day} must be positive."));

            if (dc.MergedBlocks != null)
            {
                foreach (var merged in dc.MergedBlocks)
                {
                    if (merged.BlockIndices == null || merged.BlockIndices.Count < 2)
                    {
                        errors.Add(new ValidationFailure(nameof(SchedulerOptions.DayConfigs), "Merged block must have at least two block indices."));
                        continue;
                    }
                    var indices = merged.BlockIndices.ToList();
                    indices.Sort();
                    for (int i = 1; i < indices.Count; ++i)
                    {
                        if (indices[i] == indices[i - 1])
                        {
                            errors.Add(new ValidationFailure(nameof(SchedulerOptions.DayConfigs), "Merged block contains duplicate indices."));
                            break;
                        }
                        if (indices[i] != indices[i - 1] + 1)
                        {
                            errors.Add(new ValidationFailure(nameof(SchedulerOptions.DayConfigs), "Merged block indices must be consecutive."));
                            break;
                        }
                    }
                    if (indices.Count > 0 && (indices[0] < 0 || indices[^1] >= dc.BlocksPerDay))
                        errors.Add(new ValidationFailure(nameof(SchedulerOptions.DayConfigs), $"Merged block indices for {dc.Day} out of range."));
                }
            }
        }

        if (configDays.Count != daySet.Count)
            errors.Add(new ValidationFailure(nameof(SchedulerOptions.DayConfigs), "Not all scheduling days have DayConfigs."));
        return errors;
    }

    private List<ValidationFailure> ValidateTeacherDepartments(SchedulerOptions options)
    {
        var errors = new List<ValidationFailure>();
        var coveredDepartments = new HashSet<string>(StringComparer.OrdinalIgnoreCase);

        if (options.Teachers != null)
            foreach (var teacher in options.Teachers)
                if (teacher.Departments != null)
                    foreach (var dept in teacher.Departments)
                        if (!string.IsNullOrWhiteSpace(dept))
                            coveredDepartments.Add(dept);

        if (options.TeacherDepartments != null)
            foreach (var td in options.TeacherDepartments)
                if (!string.IsNullOrWhiteSpace(td.Department))
                    coveredDepartments.Add(td.Department);

        if (options.Classes != null)
            foreach (var cls in options.Classes)
                if (!string.IsNullOrWhiteSpace(cls.Department) && !coveredDepartments.Contains(cls.Department))
                    errors.Add(new ValidationFailure(
                        nameof(SchedulerOptions.Classes),
                        $"No teacher assignment exists for department '{cls.Department}' required by class '{cls.Key}'."));
        return errors;
    }
}

public sealed class ClassValidator : AbstractValidator<Class>
{
    public ClassValidator()
    {
        RuleFor(x => x.Key).NotEmpty().WithMessage("Class must have a valid Key.");
        RuleFor(x => x.WeeklyBlocks).GreaterThan(0).WithMessage("WeeklyBlocks must be greater than zero for class {PropertyName}.");
        RuleFor(x => x.Streams).NotNull();
    }
}

public sealed class ClassStreamValidator : AbstractValidator<ClassStream>
{
    public ClassStreamValidator()
    {
        RuleFor(x => x.Id).NotEmpty().WithMessage("Stream must have a valid Id.");
        RuleFor(x => x.Size).GreaterThan(0).WithMessage("Stream must have positive size.");
    }
}

public sealed class RoomValidator : AbstractValidator<Room>
{
    public RoomValidator()
    {
        RuleFor(x => x.Id).NotEmpty().WithMessage("Room must have a valid Id.");
        RuleFor(x => x.Capacity).GreaterThan(0).WithMessage("Room must have positive capacity.");
        RuleFor(x => x.SetupTimeBuffer).GreaterThanOrEqualTo(0).WithMessage("Room must have non-negative setup time buffer.");
    }
}

public sealed class MergedBlockValidator : AbstractValidator<MergedBlock>
{
    public MergedBlockValidator()
    {
        RuleFor(x => x.BlockIndices).NotNull().NotEmpty().WithMessage("Merged block must have block indices.");
    }
}

public sealed class DayConfigValidator : AbstractValidator<DayConfig>
{
    public DayConfigValidator()
    {
        RuleFor(x => x.BlocksPerDay).GreaterThan(0).WithMessage("BlocksPerDay must be positive.");
    }
}

public sealed class TeacherDepartmentValidator : AbstractValidator<TeacherDepartment>
{
    public TeacherDepartmentValidator()
    {
        RuleFor(x => x.TeacherId).NotEmpty().WithMessage("TeacherId must not be empty.");
        RuleFor(x => x.Department).NotEmpty().WithMessage("Department must not be empty.");
    }
}

public sealed class PreAssignedSlotValidator : AbstractValidator<PreAssignedSlot>
{
    public PreAssignedSlotValidator()
    {
        RuleFor(x => x.AssignmentIndex).GreaterThanOrEqualTo(0).WithMessage("AssignmentIndex must be non-negative.");
        RuleFor(x => x.Day).GreaterThanOrEqualTo(0).WithMessage("Day must be non-negative.");
        RuleFor(x => x.Block).GreaterThanOrEqualTo(0).WithMessage("Block must be non-negative.");
    }
}