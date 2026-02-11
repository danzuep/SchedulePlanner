using Google.OrTools.Sat;

namespace SchedulePlanner
{
    internal static class Program
    {
        private static List<ILiteral> NegatedBoundedSpan(
            IReadOnlyList<BoolVar> works,
            int start,
            int length)
        {
            var sequence = new List<ILiteral>();
            if (start > 0)
            {
                sequence.Add(works[start - 1]);
            }

            for (var i = 0; i < length; ++i)
            {
                sequence.Add(works[start + i].Not());
            }

            if (start + length < works.Count)
            {
                sequence.Add(works[start + length]);
            }

            return sequence;
        }

        private static (List<BoolVar> variables, List<int> coefficients) AddSoftSequenceConstraint(
            CpModel model,
            IReadOnlyList<BoolVar> works,
            int hardMin,
            int softMin,
            int minCost,
            int softMax,
            int hardMax,
            int maxCost,
            string prefix)
        {
            var costVars = new List<BoolVar>();
            var costCoeffs = new List<int>();

            for (var length = 1; length < hardMin; ++length)
            {
                for (var start = 0; start <= works.Count - length; ++start)
                {
                    model.AddBoolOr(NegatedBoundedSpan(works, start, length));
                }
            }

            if (minCost > 0)
            {
                for (var length = hardMin; length < softMin; ++length)
                {
                    for (var start = 0; start <= works.Count - length; ++start)
                    {
                        var span = NegatedBoundedSpan(works, start, length);
                        var name = $": under_span(start={start}, length={length})";
                        var lit = model.NewBoolVar(prefix + name);
                        span.Add(lit);
                        model.AddBoolOr(span);
                        costVars.Add(lit);
                        costCoeffs.Add(minCost * (softMin - length));
                    }
                }
            }

            if (maxCost > 0)
            {
                for (var length = softMax + 1; length <= hardMax; ++length)
                {
                    for (var start = 0; start <= works.Count - length; ++start)
                    {
                        var span = NegatedBoundedSpan(works, start, length);
                        var name = $": over_span(start={start}, length={length})";
                        var lit = model.NewBoolVar(prefix + name);
                        span.Add(lit);
                        model.AddBoolOr(span);
                        costVars.Add(lit);
                        costCoeffs.Add(maxCost * (length - softMax));
                    }
                }
            }

            for (var start = 0; start <= works.Count - hardMax - 1; ++start)
            {
                var sequence = new List<ILiteral>();
                for (var i = start; i < start + hardMax + 1; ++i)
                {
                    sequence.Add(works[i].Not());
                }

                model.AddBoolOr(sequence);
            }

            return (costVars, costCoeffs);
        }

        private static (List<IntVar> variables, List<int> coefficients) AddSoftSumConstraint(
            CpModel model,
            IReadOnlyList<BoolVar> works,
            int hardMin,
            int softMin,
            int minCost,
            int softMax,
            int hardMax,
            int maxCost,
            string prefix)
        {
            var costVars = new List<IntVar>();
            var costCoeffs = new List<int>();
            var sumVar = model.NewIntVar(hardMin, hardMax, "");
            model.Add(sumVar == LinearExpr.Sum(works));

            if (softMin > hardMin && minCost > 0)
            {
                var delta = model.NewIntVar(-works.Count, works.Count, "");
                model.Add(delta == softMin - sumVar);
                var excess = model.NewIntVar(0, works.Count, prefix + ": under_sum");
                model.AddMaxEquality(excess, new[] { delta, model.NewConstant(0) });
                costVars.Add(excess);
                costCoeffs.Add(minCost);
            }

            if (softMax < hardMax && maxCost > 0)
            {
                var delta = model.NewIntVar(-works.Count, works.Count, "");
                model.Add(delta == sumVar - softMax);
                var excess = model.NewIntVar(0, works.Count, prefix + ": over_sum");
                model.AddMaxEquality(excess, new[] { delta, model.NewConstant(0) });
                costVars.Add(excess);
                costCoeffs.Add(maxCost);
            }

            return (costVars, costCoeffs);
        }

        private static void SolveShiftScheduling(string parameters, string outputProto)
        {
            const int numEmployees = 8;
            const int numWeeks = 3;
            // O=Off, M=Morning, A=Afternoon, N=Night
            var shifts = new[] { "O", "M", "A", "N" };

            var fixedAssignments = new (int employee, int shift, int day)[]
            {
                (0, 0, 0),
                (1, 0, 0),
                (2, 1, 0),
                (3, 1, 0),
                (4, 2, 0),
                (5, 2, 0),
                (6, 2, 3),
                (7, 3, 0),
                (0, 1, 1),
                (1, 1, 1),
                (2, 2, 1),
                (3, 2, 1),
                (4, 2, 1),
                (5, 0, 1),
                (6, 0, 1),
                (7, 3, 1),
            };

            var requests = new (int employee, int shift, int day, int weight)[]
            {
                (3, 0, 5, -2),
                (5, 3, 10, -2),
                (2, 3, 4, 4),
            };

            var shiftConstraints = new (int shift, int hardMin, int softMin, int minCost, int softMax, int hardMax, int maxCost)[]
            {
                (0, 1, 1, 0, 2, 2, 0),
                (3, 1, 2, 20, 3, 4, 5),
            };

            var weeklySumConstraints = new (int shift, int hardMin, int softMin, int minCost, int softMax, int hardMax, int maxCost)[]
            {
                (0, 1, 2, 7, 2, 3, 4),
                (3, 0, 1, 3, 4, 4, 0),
            };

            var penalizedTransitions = new (int previousShift, int nextShift, int penalty)[]
            {
                (2, 3, 4),
                (3, 1, 0),
            };

            var weeklyCoverDemands = new (int morning, int afternoon, int night)[]
            {
                (2, 3, 1),
                (2, 3, 1),
                (2, 2, 2),
                (2, 3, 1),
                (2, 2, 2),
                (1, 2, 3),
                (1, 3, 1),
            };

            var excessCoverPenalties = new[] { 2, 2, 5 };

            var numDays = numWeeks * 7;
            var numShifts = shifts.Length;

            var model = new CpModel();

            var work = new BoolVar[numEmployees, numShifts, numDays];
            for (var e = 0; e < numEmployees; ++e)
                for (var s = 0; s < numShifts; ++s)
                    for (var d = 0; d < numDays; ++d)
                    {
                        work[e, s, d] = model.NewBoolVar($"work{e}_{s}_{d}");
                    }

            var objBoolVars = new List<BoolVar>();
            var objBoolCoeffs = new List<int>();
            var objIntVars = new List<IntVar>();
            var objIntCoeffs = new List<int>();

            for (var e = 0; e < numEmployees; ++e)
                for (var d = 0; d < numDays; ++d)
                {
                    var dailyAssignments = new List<ILiteral>();
                    for (var s = 0; s < numShifts; ++s)
                    {
                        dailyAssignments.Add(work[e, s, d]);
                    }

                    model.AddExactlyOne(dailyAssignments);
                }

            foreach (var (employee, shift, day) in fixedAssignments)
            {
                model.Add(work[employee, shift, day] == 1);
            }

            foreach (var (employee, shift, day, weight) in requests)
            {
                objBoolVars.Add(work[employee, shift, day]);
                objBoolCoeffs.Add(weight);
            }

            foreach (var ct in shiftConstraints)
            {
                var (shift, hardMin, softMin, minCost, softMax, hardMax, maxCost) = ct;
                for (var e = 0; e < numEmployees; ++e)
                {
                    var works = Enumerable.Range(0, numDays)
                        .Select(d => work[e, shift, d])
                        .ToList();
                    var (vars, coeffs) = AddSoftSequenceConstraint(
                        model,
                        works,
                        hardMin,
                        softMin,
                        minCost,
                        softMax,
                        hardMax,
                        maxCost,
                        $"shift_constraint(employee {e}, shift {shift})");
                    objBoolVars.AddRange(vars);
                    objBoolCoeffs.AddRange(coeffs);
                }
            }

            foreach (var ct in weeklySumConstraints)
            {
                var (shift, hardMin, softMin, minCost, softMax, hardMax, maxCost) = ct;
                for (var e = 0; e < numEmployees; ++e)
                    for (var w = 0; w < numWeeks; ++w)
                    {
                        var works = Enumerable.Range(0, 7)
                            .Select(d => work[e, shift, d + w * 7])
                            .ToList();
                        var (vars, coeffs) = AddSoftSumConstraint(
                            model,
                            works,
                            hardMin,
                            softMin,
                            minCost,
                            softMax,
                            hardMax,
                            maxCost,
                            $"weekly_sum_constraint(employee {e}, shift {shift}, week {w})");
                        objIntVars.AddRange(vars);
                        objIntCoeffs.AddRange(coeffs);
                    }
            }

            foreach (var (previousShift, nextShift, cost) in penalizedTransitions)
            {
                for (var e = 0; e < numEmployees; ++e)
                    for (var d = 0; d < numDays - 1; ++d)
                    {
                        var transition = new List<ILiteral>
                    {
                        work[e, previousShift, d].Not(),
                        work[e, nextShift, d + 1].Not()
                    };

                        if (cost == 0)
                        {
                            model.AddBoolOr(transition);
                        }
                        else
                        {
                            var transVar = model.NewBoolVar($"transition (employee={e}, day={d})");
                            transition.Add(transVar);
                            model.AddBoolOr(transition);
                            objBoolVars.Add(transVar);
                            objBoolCoeffs.Add(cost);
                        }
                    }
            }

            for (var s = 1; s < numShifts; ++s)
                for (var w = 0; w < numWeeks; ++w)
                    for (var d = 0; d < 7; ++d)
                    {
                        var works = Enumerable.Range(0, numEmployees)
                            .Select(e => work[e, s, w * 7 + d])
                            .ToList();

                        var minDemand = s switch
                        {
                            1 => weeklyCoverDemands[d].morning,
                            2 => weeklyCoverDemands[d].afternoon,
                            3 => weeklyCoverDemands[d].night,
                            _ => throw new ArgumentOutOfRangeException()
                        };

                        var worked = model.NewIntVar(minDemand, numEmployees, "");
                        model.Add(worked == LinearExpr.Sum(works));
                        var overPenalty = excessCoverPenalties[s - 1];
                        if (overPenalty > 0)
                        {
                            var name = $"excess_demand(shift={s}, week={w}, day={d})";
                            var excess = model.NewIntVar(0, numEmployees - minDemand, name);
                            model.Add(excess == worked - minDemand);
                            objIntVars.Add(excess);
                            objIntCoeffs.Add(overPenalty);
                        }
                    }

            var objective = new List<LinearExpr>();
            var objectiveCoeffs = new List<int>();

            objective.AddRange(objBoolVars);
            objectiveCoeffs.AddRange(objBoolCoeffs);

            objective.AddRange(objIntVars);
            objectiveCoeffs.AddRange(objIntCoeffs);

            var linearObjective = LinearExpr.WeightedSum(objective, objectiveCoeffs);
            model.Minimize(linearObjective);

            if (!string.IsNullOrEmpty(outputProto))
            {
                Console.WriteLine($"Writing proto to {outputProto}");
                File.WriteAllText(outputProto, model.ToString());
            }

            var solver = new CpSolver();
            if (!string.IsNullOrEmpty(parameters))
            {
                solver.StringParameters = parameters;
            }

            var status = solver.Solve(model);

            if (status == CpSolverStatus.Optimal || status == CpSolverStatus.Feasible)
            {
                Console.WriteLine();
                var header = "          ";
                for (var w = 0; w < numWeeks; ++w)
                {
                    header += "M T W T F S S ";
                }

                Console.WriteLine(header);
                for (var e = 0; e < numEmployees; ++e)
                {
                    var schedule = string.Empty;
                    for (var d = 0; d < numDays; ++d)
                        for (var s = 0; s < numShifts; ++s)
                        {
                            if (solver.BooleanValue(work[e, s, d]))
                            {
                                schedule += $"{shifts[s]} ";
                            }
                        }

                    Console.WriteLine($"worker {e}: {schedule}");
                }

                Console.WriteLine();
                Console.WriteLine("Penalties:");
                for (var i = 0; i < objBoolVars.Count; ++i)
                {
                    if (solver.BooleanValue(objBoolVars[i]))
                    {
                        var penalty = objBoolCoeffs[i];
                        if (penalty > 0)
                        {
                            Console.WriteLine($"  {objBoolVars[i].Name()} violated, penalty={penalty}");
                        }
                        else
                        {
                            Console.WriteLine($"  {objBoolVars[i].Name()} fulfilled, gain={-penalty}");
                        }
                    }
                }

                for (var i = 0; i < objIntVars.Count; ++i)
                {
                    if (solver.Value(objIntVars[i]) > 0)
                    {
                        Console.WriteLine(
                            $"  {objIntVars[i].Name()} violated by {solver.Value(objIntVars[i])}, "
                            + $"linear penalty={objIntCoeffs[i]}");
                    }
                }
            }

            Console.WriteLine();
            Console.WriteLine(solver.ResponseStats());
        }

        private static void Main(string[] args)
        {
            var parameters = args.Length > 0 ? args[0] : "max_time_in_seconds:10.0";
            var outputProto = args.Length > 1 ? args[1] : string.Empty;
            SolveShiftScheduling(parameters, outputProto);
            Console.ReadLine();
        }
    }
}