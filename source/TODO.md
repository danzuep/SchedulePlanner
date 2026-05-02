# Timetabling Enhancements Checklist

## Block Period Enhancements
<!-- - [ ] Support ordering classrooms by distance/time relative to student hubs, then the distance/time from those hubs to the next hub. -->

## Usability & Operational Features
- [x] Replace messy if statements with FluentValidation to define complex business rules for your school data
- [ ] Improve the UI with Syncfusion or DevExpress (Scheduler Controls): These libraries offer out-of-the-box support for drag-and-drop, "timeline views" for teachers, and "resource views" for classrooms.

## Temporal Integration
- [x] Integrate Temporal for reliable long-running scheduling workflows
  - [x] Create Temporal activity for CP-SAT solver execution with heartbeat support
  - [x] Implement real-time progress reporting (current gap, objective value) to UI
  - [x] Add graceful shutdown handling via Temporal signals  
  - [x] Design workflow for incremental re-solving on schedule changes
- [x] Add temporal-aware scheduling features
  - [x] Support scheduling over multiple temporal horizons (day/week/term) via DayConfigs with variable BlocksPerDay
  - [x] Implement temporal dependencies between scheduling decisions via PreAssignedSlots and PreviousScheduleResult
  - [x] Add temporal fault tolerance and recovery mechanisms via Temporal retry policies and checkpointing
