# Timetabling Enhancements Checklist

## Block Period Enhancements
<!-- - [ ] Support ordering classrooms by distance/time relative to student hubs, then the distance/time from those hubs to the next hub. -->

## CLI testability
- [x] Move the core "Run Demo Schedule" functionality from WPF down into SchedulePlanner.Cli so we can run it in an integration test and export the results to Excel from there.

## Usability & Operational Features - WPF
- [x] Move the status card to the Data tab
- [x] Fix the "Run Demo Schedule" button. "No service for type IConfigValidator has been registered." The result should display in the "Schedule Timeline" card.
