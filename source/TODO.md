# K-12 Enhancements Checklist

## Block Period Enhancements
- [x] Support common teacher planning blocks or team co-teaching in OptimizationBuilder
  - [x] Extend Class model to support multiple teacher IDs (co-teaching)
  - [x] Update ClassAssignmentBuilder to handle multiple teachers per class
  - [x] Add constraints for co-teaching (teachers available at same time)
  - [x] Add penalty for common planning blocks (teachers having overlapping free time)
  - [x] Update results to show co-teachers
- [x] Support teachers sharing classrooms
<!-- - [ ] Support ordering classrooms by distance/time relative to student hubs, then the distance/time from those hubs to the next hub. -->

## Usability & Operational Features
- [x] Implement partial/incremental solving and "what-if" scenario support
  - [x] Add PreAssignedSlots to SchedulerOptions (dictionary of fixed assignments)
  - [x] Modify SchedulingService to accept and fix pre-assigned variables
  - [x] Add incremental solving: load previous solution and adjust for changes
  - [x] Add what-if support: clone options, modify, solve with partial reuse
  - [x] Add result comparison for what-if scenarios

## General Improvements
- [ ] Support hybrid schedules (mix of traditional and block periods)
  - [x] Extend SchedulerOptions with DayConfigs (per day blocks, merged blocks)
  - [ ] Update SchedulingContext to handle variable blocks per day
  - [ ] Modify decision variables to be jagged array [day][block]
  - [ ] Update all constraints and optimizations for variable blocks
  - [x] Add validation for day configs
  - [ ] Update results to handle variable blocks per day
- [x] Break advanced refactorings down into smaller tasks (common planning blocks, partial solving, hybrid schedules)
- [x] Analyse the project and create TODOs for architectural and maintainability improvements.
  - [x] Add comprehensive unit tests for all builders and validators
  - [x] Refactor large methods in OptimizationBuilder into smaller, focused methods
  - [x] Add integration tests for end-to-end scheduling scenarios
  - [x] Implement dependency injection for better testability
  - [x] Add performance benchmarks for solver times
  - [x] Create a configuration schema validation
  - [x] Add logging for solver performance metrics