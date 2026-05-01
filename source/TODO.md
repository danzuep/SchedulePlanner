# K-12 Enhancements Checklist

## Block Period Enhancements
<!-- - [ ] Support ordering classrooms by distance/time relative to student hubs, then the distance/time from those hubs to the next hub. -->

## Usability & Operational Features

## General Improvements
- [x] Use system diagnostics activity and metrics for OpenTelemetry-compatible diagnostics
- [ ] Support hybrid schedules (mix of traditional and block periods)
  - [x] Extend SchedulerOptions with DayConfigs (per day blocks, merged blocks)
  - [x] Update SchedulingContext to handle variable blocks per day
  - [x] Modify decision variables to be jagged array [day][block]
  - [x] Update all constraints and optimizations for variable blocks
  - [x] Add validation for day configs
  - [x] Update results to handle variable blocks per day
- [x] Make the GenerateLargeK12School scenario more realistic for a secondary school instead of just four classes, and realistic subjects for the highschool students to take.
- [x] Update all the projects with the new behaviour, and add basic tests for all the projects that don't have test projects yet.