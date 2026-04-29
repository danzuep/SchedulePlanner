using Google.OrTools.Sat;

namespace SchedulePlanner.Core
{
    public interface IOptimizationBuilder
    {
        IReadOnlyList<RoomChangePenalty> AddRoomChangeOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int roomChangePenaltyWeight,
            CancellationToken cancellationToken);

        IReadOnlyList<ScheduleSpreadPenalty> AddScheduleSpreadOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int scheduleSpreadPenaltyWeight,
            CancellationToken cancellationToken);

        IReadOnlyList<WeekDistributionPenalty> AddWeekDistributionOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int weekDistributionPenaltyWeight,
            CancellationToken cancellationToken);

        IReadOnlyList<ClassDayClusteringPenalty> AddClassDayClusteringOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int classDayClusteringPenaltyWeight,
            CancellationToken cancellationToken);

        IReadOnlyList<ClassBlockConsistencyPenalty> AddClassBlockConsistencyOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int classBlockConsistencyPenaltyWeight,
            CancellationToken cancellationToken);

        IReadOnlyList<StreamFragmentationPenalty> AddStreamFragmentationOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int streamFragmentationPenaltyWeight,
            CancellationToken cancellationToken);

        IReadOnlyList<SharedRoomChangePenalty> AddSharedRoomChangeOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int sharedRoomChangePenaltyWeight,
            CancellationToken cancellationToken);

        IReadOnlyList<TargetLoadAdherencePenalty> AddTargetLoadAdherenceOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int targetLoadAdherencePenaltyWeight,
            CancellationToken cancellationToken);

        IReadOnlyList<StudentRoomTransitionPenalty> AddStudentRoomTransitionOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int studentRoomTransitionPenaltyWeight,
            CancellationToken cancellationToken);

        IReadOnlyList<MergedBlockConsistencyPenalty> AddMergedBlockConsistencyOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int mergedBlockConsistencyPenaltyWeight,
            CancellationToken cancellationToken);

        IReadOnlyList<FreeTimePenalty> AddFreeTimeOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int freeTimePenaltyWeight,
            CancellationToken cancellationToken);

        IReadOnlyList<CommonPlanningPenalty> AddCommonPlanningOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int commonPlanningPenaltyWeight,
            CancellationToken cancellationToken);
    }

    public sealed class OptimizationBuilder : IOptimizationBuilder
    {
        public IReadOnlyList<RoomChangePenalty> AddRoomChangeOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int roomChangePenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<RoomChangePenalty>();

            for (var day = 0; day < context.NumDays; ++day)
            {
                cancellationToken.ThrowIfCancellationRequested();

                for (var block = 0; block < context.BlocksPerDayList[day] - 1; ++block)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    foreach (var teacherEntry in context.TeacherGroups)
                    {
                        cancellationToken.ThrowIfCancellationRequested();

                        var teacherId = teacherEntry.Key;
                        var classes = teacherEntry.Value.Classes;

                        foreach (var current in classes)
                        {
                            cancellationToken.ThrowIfCancellationRequested();

                            foreach (var next in classes)
                            {
                                cancellationToken.ThrowIfCancellationRequested();

                                if (current.Room == next.Room)
                                {
                                    continue;
                                }

                                var penaltyVar = context.Model.NewBoolVar(
                                    $"room_change_{teacherId}_day{day}_block{block}_{current.Config.Key}_{next.Config.Key}");

                                context.Model.Add(penaltyVar <= variables.Assignment[current.Index][day][block]);
                                context.Model.Add(penaltyVar <= variables.Assignment[next.Index][day][block + 1]);
                                context.Model.Add(
                                    penaltyVar >= variables.Assignment[current.Index][day][block]
                                                 + variables.Assignment[next.Index][day][block + 1]
                                                 - 1);

                                penalties.Add(new RoomChangePenalty(
                                    penaltyVar,
                                    teacherId,
                                    config.Days[day],
                                    block,
                                    current.Config.Key,
                                    current.Room,
                                    next.Config.Key,
                                    next.Room));
                            }
                        }
                    }
                }
            }

            return penalties;
        }

        public IReadOnlyList<ScheduleSpreadPenalty> AddScheduleSpreadOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int scheduleSpreadPenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<ScheduleSpreadPenalty>();

            for (var day = 0; day < context.NumDays; ++day)
            {
                cancellationToken.ThrowIfCancellationRequested();

                for (var block = 0; block < context.BlocksPerDayList[day] - 1; ++block)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    foreach (var teacherEntry in context.TeacherGroups)
                    {
                        cancellationToken.ThrowIfCancellationRequested();

                        var teacherId = teacherEntry.Key;
                        var classes = teacherEntry.Value.Classes;

                        foreach (var current in classes)
                        {
                            cancellationToken.ThrowIfCancellationRequested();

                            foreach (var next in classes)
                            {
                                cancellationToken.ThrowIfCancellationRequested();

                                if (current == next)
                                {
                                    continue;
                                }

                                var penaltyVar = context.Model.NewBoolVar(
                                    $"schedule_spread_{teacherId}_day{day}_block{block}_{current.Config.Key}_{next.Config.Key}");

                                context.Model.Add(penaltyVar <= variables.Assignment[current.Index][day][block]);
                                context.Model.Add(penaltyVar <= variables.Assignment[next.Index][day][block + 1]);
                                context.Model.Add(
                                    penaltyVar >= variables.Assignment[current.Index][day][block]
                                                 + variables.Assignment[next.Index][day][block + 1]
                                                 - 1);

                                penalties.Add(new ScheduleSpreadPenalty(
                                    penaltyVar,
                                    teacherId,
                                    config.Days[day],
                                    block,
                                    current.Config.Key,
                                    next.Config.Key));
                            }
                        }
                    }
                }
            }

            return penalties;
        }

        public IReadOnlyList<WeekDistributionPenalty> AddWeekDistributionOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int weekDistributionPenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<WeekDistributionPenalty>();

            foreach (var teacherEntry in context.TeacherGroups)
            {
                cancellationToken.ThrowIfCancellationRequested();

                var teacherId = teacherEntry.Key;
                var classes = teacherEntry.Value.Classes;

                for (var d = 0; d < context.NumDays - 1; ++d)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    var sumDayD = new List<LinearExpr>();
                    var sumDayD1 = new List<LinearExpr>();

                    foreach (var cls in classes)
                    {
                        for (var block = 0; block < context.BlocksPerDay; ++block)
                        {
                            sumDayD.Add(variables.Assignment[cls.Index, d, block]);
                            sumDayD1.Add(variables.Assignment[cls.Index, d + 1, block]);
                        }
                    }

                    var penaltyVar = context.Model.NewBoolVar(
                        $"week_distribution_{teacherId}_day{d}_to_day{d + 1}");

                    context.Model.Add(LinearExpr.Sum(sumDayD1) >= LinearExpr.Sum(sumDayD) + 1).OnlyEnforceIf(penaltyVar);
                    context.Model.Add(LinearExpr.Sum(sumDayD1) < LinearExpr.Sum(sumDayD) + 1).OnlyEnforceIf(penaltyVar.Not());

                    penalties.Add(new WeekDistributionPenalty(
                        penaltyVar,
                        teacherId,
                        config.Days[d],
                        config.Days[d + 1]));
                }
            }

            return penalties;
        }

        public IReadOnlyList<ClassDayClusteringPenalty> AddClassDayClusteringOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int classDayClusteringPenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<ClassDayClusteringPenalty>();

            foreach (var classAssignment in context.ClassAssignments)
            {
                cancellationToken.ThrowIfCancellationRequested();

                for (var day = 0; day < context.NumDays; ++day)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    var daySlots = new List<LinearExpr>();
                    for (var block = 0; block < context.BlocksPerDay; ++block)
                    {
                        daySlots.Add(variables.Assignment[classAssignment.Index, day, block]);
                    }

                    var penaltyVar = context.Model.NewBoolVar(
                        $"class_day_clustering_{classAssignment.Config.Key}_day{day}");

                    context.Model.Add(LinearExpr.Sum(daySlots) >= 2).OnlyEnforceIf(penaltyVar);
                    context.Model.Add(LinearExpr.Sum(daySlots) < 2).OnlyEnforceIf(penaltyVar.Not());

                    penalties.Add(new ClassDayClusteringPenalty(
                        penaltyVar,
                        classAssignment.Config.Key,
                        config.Days[day]));
                }
            }

            return penalties;
        }

        public IReadOnlyList<ClassBlockConsistencyPenalty> AddClassBlockConsistencyOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int classBlockConsistencyPenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<ClassBlockConsistencyPenalty>();

            foreach (var classAssignment in context.ClassAssignments)
            {
                cancellationToken.ThrowIfCancellationRequested();

                for (var block = 0; block < context.BlocksPerDay; ++block)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    var blockAssignments = new List<LinearExpr>();
                    for (var day = 0; day < context.NumDays; ++day)
                    {
                        blockAssignments.Add(variables.Assignment[classAssignment.Index, day, block]);
                    }

                    var penaltyVar = context.Model.NewBoolVar(
                        $"class_block_consistency_{classAssignment.Config.Key}_block{block}");

                    context.Model.Add(LinearExpr.Sum(blockAssignments) >= 1).OnlyEnforceIf(penaltyVar);
                    context.Model.Add(LinearExpr.Sum(blockAssignments) < 1).OnlyEnforceIf(penaltyVar.Not());

                    penalties.Add(new ClassBlockConsistencyPenalty(
                        penaltyVar,
                        classAssignment.Config.Key,
                        block));
                }
            }

            return penalties;
        }

        public IReadOnlyList<StreamFragmentationPenalty> AddStreamFragmentationOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int streamFragmentationPenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<StreamFragmentationPenalty>();

            foreach (var classAssignment in context.ClassAssignments.Where(a => a.ClassStream != null))
            {
                cancellationToken.ThrowIfCancellationRequested();

                for (var block = 0; block < context.BlocksPerDay; ++block)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    var blockAssignments = new List<LinearExpr>();
                    for (var day = 0; day < context.NumDays; ++day)
                    {
                        blockAssignments.Add(variables.Assignment[classAssignment.Index, day, block]);
                    }

                    var penaltyVar = context.Model.NewBoolVar(
                        $"stream_fragmentation_{classAssignment.ClassStream!.Id}_block{block}");

                    context.Model.Add(LinearExpr.Sum(blockAssignments) >= 1).OnlyEnforceIf(penaltyVar);
                    context.Model.Add(LinearExpr.Sum(blockAssignments) < 1).OnlyEnforceIf(penaltyVar.Not());

                    penalties.Add(new StreamFragmentationPenalty(
                        penaltyVar,
                        classAssignment.ClassStream.Id,
                        block));
                }
            }

            return penalties;
        }

        public IReadOnlyList<SharedRoomChangePenalty> AddSharedRoomChangeOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int sharedRoomChangePenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<SharedRoomChangePenalty>();

            for (var day = 0; day < context.NumDays; ++day)
            {
                cancellationToken.ThrowIfCancellationRequested();

                for (var block = 0; block < context.BlocksPerDay - 1; ++block)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    foreach (var teacherEntry in context.TeacherGroups)
                    {
                        cancellationToken.ThrowIfCancellationRequested();

                        var teacherId = teacherEntry.Key;
                        var classes = teacherEntry.Value.Classes;

                        foreach (var current in classes)
                        {
                            cancellationToken.ThrowIfCancellationRequested();

                            foreach (var next in classes)
                            {
                                cancellationToken.ThrowIfCancellationRequested();

                                if (current.Room == next.Room || (!IsSharedRoom(config, current.Room) && !IsSharedRoom(config, next.Room)))
                                {
                                    continue;
                                }

                                var penaltyVar = context.Model.NewBoolVar(
                                    $"shared_room_change_{teacherId}_day{day}_block{block}_{current.Config.Key}_{next.Config.Key}");

                                context.Model.Add(penaltyVar <= variables.Assignment[current.Index, day, block]);
                                context.Model.Add(penaltyVar <= variables.Assignment[next.Index, day, block + 1]);
                                context.Model.Add(
                                    penaltyVar >= variables.Assignment[current.Index, day, block]
                                                 + variables.Assignment[next.Index, day, block + 1]
                                                 - 1);

                                penalties.Add(new SharedRoomChangePenalty(
                                    penaltyVar,
                                    teacherId,
                                    config.Days[day],
                                    block,
                                    current.Config.Key,
                                    current.Room,
                                    next.Config.Key,
                                    next.Room));
                            }
                        }
                    }
                }
            }

            return penalties;
        }

        public IReadOnlyList<StudentRoomTransitionPenalty> AddStudentRoomTransitionOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int studentRoomTransitionPenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<StudentRoomTransitionPenalty>();

            for (var day = 0; day < context.NumDays; ++day)
            {
                cancellationToken.ThrowIfCancellationRequested();

                for (var block = 0; block < context.BlocksPerDay - 1; ++block)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    foreach (var assignment in context.ClassAssignments.Where(a => a.ClassStream != null))
                    {
                        cancellationToken.ThrowIfCancellationRequested();

                        var stream = assignment.ClassStream!;
                        var nextAssignments = context.ClassAssignments.Where(a => a.ClassStream != null && a.ClassStream!.Id == stream.Id && a != assignment);

                        foreach (var next in nextAssignments)
                        {
                            if (assignment.Room == next.Room)
                            {
                                continue;
                            }

                            var penaltyVar = context.Model.NewBoolVar(
                                $"student_room_transition_{stream.Id}_day{day}_block{block}_{assignment.Config.Key}_{next.Config.Key}");

                            context.Model.Add(penaltyVar <= variables.Assignment[assignment.Index, day, block]);
                            context.Model.Add(penaltyVar <= variables.Assignment[next.Index, day, block + 1]);
                            context.Model.Add(
                                penaltyVar >= variables.Assignment[assignment.Index, day, block]
                                             + variables.Assignment[next.Index, day, block + 1]
                                             - 1);

                            penalties.Add(new StudentRoomTransitionPenalty(
                                penaltyVar,
                                stream.Id,
                                config.Days[day],
                                block,
                                assignment.Config.Key,
                                assignment.Room,
                                next.Config.Key,
                                next.Room));
                        }
                    }
                }
            }

            return penalties;
        }

        public IReadOnlyList<MergedBlockConsistencyPenalty> AddMergedBlockConsistencyOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int mergedBlockConsistencyPenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<MergedBlockConsistencyPenalty>();

            if (config.MergedBlocks == null) return penalties;

            foreach (var merged in config.MergedBlocks)
            {
                cancellationToken.ThrowIfCancellationRequested();

                for (var day = 0; day < context.NumDays; ++day)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    for (var i = 0; i < merged.BlockIndices.Count - 1; ++i)
                    {
                        var currentBlock = merged.BlockIndices[i];
                        var nextBlock = merged.BlockIndices[i + 1];

                        foreach (var assignment in context.ClassAssignments)
                        {
                            foreach (var otherAssignment in context.ClassAssignments)
                            {
                                if (assignment == otherAssignment) continue;

                                var penaltyVar = context.Model.NewBoolVar(
                                    $"merged_consistency_{assignment.Index}_{otherAssignment.Index}_day{day}_block{currentBlock}_to_{nextBlock}");

                                context.Model.Add(penaltyVar <= variables.Assignment[assignment.Index, day, currentBlock]);
                                context.Model.Add(penaltyVar <= variables.Assignment[otherAssignment.Index, day, nextBlock]);
                                context.Model.Add(
                                    penaltyVar >= variables.Assignment[assignment.Index, day, currentBlock]
                                                 + variables.Assignment[otherAssignment.Index, day, nextBlock]
                                                 - 1);

                                penalties.Add(new MergedBlockConsistencyPenalty(
                                    penaltyVar,
                                    merged.BlockIndices.ToArray(),
                                    config.Days[day],
                                    currentBlock,
                                    nextBlock,
                                    assignment.Config.Key,
                                    otherAssignment.Config.Key));
                            }
                        }
                    }
                }
            }

            return penalties;
        }

        public IReadOnlyList<FreeTimePenalty> AddFreeTimeOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int freeTimePenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<FreeTimePenalty>();

            foreach (var teacherEntry in context.TeacherGroups)
            {
                cancellationToken.ThrowIfCancellationRequested();

                var teacher = teacherEntry.Value.Teacher;
                var classes = teacherEntry.Value.Classes;

                var totalBlocks = context.NumDays * context.BlocksPerDayList.Sum(); // Note: assuming constant for now
                var minFree = totalBlocks / 2; // Example: at least half free

                var assignedBlocks = new List<LinearExpr>();
                foreach (var cls in classes)
                {
                    for (var day = 0; day < context.NumDays; ++day)
                    {
                        for (var block = 0; block < context.BlocksPerDayList[day]; ++block)
                        {
                            assignedBlocks.Add(variables.Assignment[cls.Index][day][block]);
                        }
                    }
                }

                var assignedSum = LinearExpr.Sum(assignedBlocks);

                var penaltyVar = context.Model.NewBoolVar(
                    $"free_time_{teacher.Id}");

                context.Model.Add(assignedSum >= totalBlocks - minFree + 1).OnlyEnforceIf(penaltyVar);
                context.Model.Add(assignedSum < totalBlocks - minFree + 1).OnlyEnforceIf(penaltyVar.Not());

                penalties.Add(new FreeTimePenalty(
                    penaltyVar,
                    teacher.Id,
                    totalBlocks - minFree));
            }

            return penalties;
        }

        private static bool IsSharedRoom(SchedulerOptions config, string roomId)
        {
            return config.Rooms.FirstOrDefault(r => r.Id == roomId)?.IsShared ?? false;
        }

        public IReadOnlyList<TargetLoadAdherencePenalty> AddTargetLoadAdherenceOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int targetLoadAdherencePenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<TargetLoadAdherencePenalty>();

            foreach (var teacherEntry in context.TeacherGroups)
            {
                cancellationToken.ThrowIfCancellationRequested();

                var teacher = teacherEntry.Value.Teacher;
                var classes = teacherEntry.Value.Classes;

                var totalBlocks = new List<LinearExpr>();
                foreach (var cls in classes)
                {
                    for (var day = 0; day < context.NumDays; ++day)
                    {
                        for (var block = 0; block < context.BlocksPerDay; ++block)
                        {
                            totalBlocks.Add(variables.Assignment[cls.Index, day, block]);
                        }
                    }
                }

                var totalSum = LinearExpr.Sum(totalBlocks);

                // Penalize deviation from target
                // For under-assignment
                var underPenaltyVar = context.Model.NewBoolVar(
                    $"target_load_under_{teacher.Id}");
                context.Model.Add(totalSum >= teacher.TargetLoadBlocks).OnlyEnforceIf(underPenaltyVar.Not());
                context.Model.Add(totalSum < teacher.TargetLoadBlocks).OnlyEnforceIf(underPenaltyVar);

                penalties.Add(new TargetLoadAdherencePenalty(
                    underPenaltyVar,
                    teacher.Id,
                    teacher.TargetLoadBlocks,
                    true)); // true for under

                // For over-assignment
                var overPenaltyVar = context.Model.NewBoolVar(
                    $"target_load_over_{teacher.Id}");
                context.Model.Add(totalSum <= teacher.TargetLoadBlocks).OnlyEnforceIf(overPenaltyVar.Not());
                context.Model.Add(totalSum > teacher.TargetLoadBlocks).OnlyEnforceIf(overPenaltyVar);

                penalties.Add(new TargetLoadAdherencePenalty(
                    overPenaltyVar,
                    teacher.Id,
                    teacher.TargetLoadBlocks,
                    false)); // false for over
            }

            return penalties;
        }

        public IReadOnlyList<CommonPlanningPenalty> AddCommonPlanningOptimization(
            SchedulingContext context,
            ScheduleVariables variables,
            SchedulerOptions config,
            int commonPlanningPenaltyWeight,
            CancellationToken cancellationToken)
        {
            var penalties = new List<CommonPlanningPenalty>();

            // Collect unique co-teaching pairs
            var coTeachingPairs = new HashSet<(string, string)>();
            foreach (var assignment in context.ClassAssignments)
            {
                if (assignment.Teachers.Count > 1)
                {
                    var teacherIds = assignment.Teachers.Select(t => t.Id).OrderBy(id => id).ToList();
                    for (var i = 0; i < teacherIds.Count; ++i)
                    {
                        for (var j = i + 1; j < teacherIds.Count; ++j)
                        {
                            coTeachingPairs.Add((teacherIds[i], teacherIds[j]));
                        }
                    }
                }
            }

            foreach (var (teacher1Id, teacher2Id) in coTeachingPairs)
            {
                var teacher1 = context.TeacherGroups[teacher1Id];
                var teacher2 = context.TeacherGroups[teacher2Id];

                for (var dayIndex = 0; dayIndex < context.NumDays; ++dayIndex)
                {
                    cancellationToken.ThrowIfCancellationRequested();

                    var day = config.Days[dayIndex];

                    // Create BoolVars for free status
                    var free1Vars = new BoolVar[context.BlocksPerDayList[dayIndex]];
                    var free2Vars = new BoolVar[context.BlocksPerDayList[dayIndex]];

                    for (var block = 0; block < context.BlocksPerDayList[dayIndex]; ++block)
                    {
                        // Teacher1 free if no class assigned
                        var teacher1Busy = LinearExpr.Sum(teacher1.Classes.Select(cls => variables.Assignment[cls.Index][dayIndex][block]));
                        free1Vars[block] = context.Model.NewBoolVar($"free_{teacher1Id}_{dayIndex}_{block}");
                        context.Model.Add(free1Vars[block] == (teacher1Busy == 0));

                        // Teacher2 free
                        var teacher2Busy = LinearExpr.Sum(teacher2.Classes.Select(cls => variables.Assignment[cls.Index][dayIndex][block]));
                        free2Vars[block] = context.Model.NewBoolVar($"free_{teacher2Id}_{dayIndex}_{block}");
                        context.Model.Add(free2Vars[block] == (teacher2Busy == 0));
                    }

                    // Both free vars
                    var bothFreeVars = new BoolVar[context.BlocksPerDayList[dayIndex]];
                    for (var block = 0; block < context.BlocksPerDayList[dayIndex]; ++block)
                    {
                        bothFreeVars[block] = context.Model.NewBoolVar($"both_free_{teacher1Id}_{teacher2Id}_{dayIndex}_{block}");
                        context.Model.AddBoolAnd([free1Vars[block], free2Vars[block]], bothFreeVars[block]);
                    }

                    // Has overlapping free
                    var hasOverlappingFree = context.Model.NewBoolVar($"has_overlapping_free_{teacher1Id}_{teacher2Id}_{dayIndex}");
                    context.Model.AddBoolOr(bothFreeVars, hasOverlappingFree);

                    // Penalty if no overlapping
                    var penaltyVar = context.Model.NewBoolVar($"common_planning_penalty_{teacher1Id}_{teacher2Id}_{dayIndex}");
                    context.Model.Add(penaltyVar == (1 - hasOverlappingFree));

                    penalties.Add(new CommonPlanningPenalty(
                        penaltyVar,
                        teacher1Id,
                        teacher2Id,
                        day));
                }
            }

            // Add to objective
            if (penalties.Count > 0)
            {
                context.Model.Minimize(commonPlanningPenaltyWeight * LinearExpr.Sum(penalties.Select(p => p.Var)));
            }

            return penalties;
        }
    }

    public sealed record RoomChangePenalty(
        BoolVar Var,
        string TeacherId,
        DayOfWeek Day,
        int Block,
        string FromClassKey,
        string FromRoom,
        string ToClassKey,
        string ToRoom);

    public sealed record ScheduleSpreadPenalty(
        BoolVar Var,
        string TeacherId,
        DayOfWeek Day,
        int Block,
        string FromClassKey,
        string ToClassKey);

    public sealed record WeekDistributionPenalty(
        BoolVar Var,
        string TeacherId,
        DayOfWeek FromDay,
        DayOfWeek ToDay);

    public sealed record ClassDayClusteringPenalty(
        BoolVar Var,
        string ClassKey,
        DayOfWeek Day);

    public sealed record ClassBlockConsistencyPenalty(
        BoolVar Var,
        string ClassKey,
        int Block);

    public sealed record StreamFragmentationPenalty(
        BoolVar Var,
        string StreamId,
        int Block);

    public sealed record SharedRoomChangePenalty(
        BoolVar Var,
        string TeacherId,
        DayOfWeek Day,
        int Block,
        string FromClassKey,
        string FromRoom,
        string ToClassKey,
        string ToRoom);

    public sealed record TargetLoadAdherencePenalty(
        BoolVar Var,
        string TeacherId,
        int TargetLoad,
        bool IsUnderAssignment);

    public sealed record StudentRoomTransitionPenalty(
        BoolVar Var,
        string StreamId,
        DayOfWeek Day,
        int Block,
        string FromClassKey,
        string FromRoom,
        string ToClassKey,
        string ToRoom);

    public sealed record MergedBlockConsistencyPenalty(
        BoolVar Var,
        IReadOnlyList<int> MergedIndices,
        DayOfWeek Day,
        int FromBlock,
        int ToBlock,
        string FromClassKey,
        string ToClassKey);

    public sealed record FreeTimePenalty(
        BoolVar Var,
        string TeacherId,
        int MinFreeBlocks);

    public sealed record CommonPlanningPenalty(
        BoolVar Var,
        string Teacher1Id,
        string Teacher2Id,
        DayOfWeek Day);
}
