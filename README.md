# SchedulePlanner

[Download SchedulePlanner](https://danzuep.github.io/SchedulePlanner/)

SchedulePlanner is a free tool that helps schools create timetables without conflicts. It automatically schedules classes for teachers, rooms, and students using smart computer algorithms to solve tricky scheduling problems.

## Main Features

- Prevents overlaps in teacher, room, or student schedules.
- Supports traditional daily schedules and longer "block" periods.
- Allows mixing schedule types per day.
- Lets multiple teachers share classes.
- Matches classes to suitable rooms (considering size and sharing).
- Uses penalties to encourage better schedules (like fewer room changes).

## Smart Optimizations

- Minimizes room changes for teachers/students.
- Spreads classes evenly across days.
- Balances class distribution over the week.
- Keeps similar classes together in blocks.
- Allows planning time for co-teachers.
- Shows progress updates during scheduling.

## For Developers

- Includes logging compatible with OpenTelemetry.
- Uses a flexible design for adding custom rules.
- Powered by Google's OR-Tools solver.
- Has 62 tests for reliability.
- Integrates with Temporal workflows for handling long scheduling tasks with progress tracking and cancellation.

## How to Use

1. Import and edit teacher, class, room, and student data.
2. Set options like blocks per day, penalties, and time limits.
3. Run the scheduler to generate a timetable.
4. Review the schedule, conflicts, and penalties.
5. Export results to Excel or other formats.

## Download

App Demo:  
![Excel](https://raw.githubusercontent.com/danzuep/SchedulePlanner/main/resources/SchedulePlanner-Excel.gif)

[Download SchedulePlanner](https://github.com/danzuep/SchedulePlanner/releases/latest)

After downloading, right click, select Properties, then Unblock.  
![Unblock](https://raw.githubusercontent.com/danzuep/SchedulePlanner/main/resources/SchedulePlanner-Unblock.gif)

---

*Animations created with [ScreenToGif](https://www.screentogif.com/).*

*SchedulePlanner is open-source software released under the MIT License. Contributions and feedback are welcome!*
