# SchedulePlanner

[Download SchedulePlanner](https://danzuep.github.io/SchedulePlanner/)

## Overview

SchedulePlanner is a classroom scheduling application that automates the creation of conflict-free timetables for schools. It uses constraint optimization to solve complex scheduling problems involving teachers, rooms, classes, and student schedules.

## Features

### Core Capabilities
- **Conflict-free scheduling**: Automatically detects and prevents teacher, room, and student conflicts
- **Block period support**: Handle traditional daily schedules and block periods with variable lengths
- **Hybrid schedules**: Mix traditional and block period structures with per-day configuration
- **Co-teaching support**: Assign multiple teachers to streamed classes
- **Room optimization**: Match classes to appropriate rooms with capacity and sharing options
- **Penalty system**: Configurable penalties for room changes, schedule spread, and planning constraints

### Scheduling Optimizations
- Room change minimization
- Schedule spread reduction (classes distributed across days)
- Week distribution balancing
- Class block consistency
- Common planning time for co-teachers

### User Interface
- Excel-based import/export for easy data entry
- WPF desktop application for visual schedule review
- Command-line interface for automated scheduling
- Background worker service for batch processing

### Developer Features
- OpenTelemetry-compatible diagnostics
- Extensible constraint and optimization builder pattern
- OR-Tools CP-SAT solver backend
- Comprehensive test coverage (54 tests)

## Usage

1. **Import data** from Excel (teachers, classes, rooms, student schedules)
2. **Configure options**: blocks per day, penalties, time limits
3. **Generate schedule**: Run the solver to create an optimized timetable
4. **Review results**: View schedule, conflicts, and penalty assessments
5. **Export**: Save results back to Excel or other formats

## Download

App Demo:  
![Excel](https://raw.githubusercontent.com/danzuep/SchedulePlanner/main/resources/SchedulePlanner-Excel.gif)

[Download SchedulePlanner](https://github.com/danzuep/SchedulePlanner/releases/latest)

After downloading, right click, select Properties, then Unblock.  
![Unblock](https://raw.githubusercontent.com/danzuep/SchedulePlanner/main/resources/SchedulePlanner-Unblock.gif)

### Note for Users Without Excel

The software relies on Microsoft Excel, so if you don't have that installed, you can use [LibreOffice](https://www.libreoffice.org/download/download-libreoffice/) as a free alternative to open and edit spreadsheet files.

---

*Animations created with [ScreenToGif](https://www.screentogif.com/).*

*SchedulePlanner is open-source software released under the MIT License. Contributions and feedback are welcome!*
