
Build example from repository root directory:
`dotnet build source/SchedulePlanner.Core.Tests/SchedulePlanner.Core.Tests.csproj --nologo -v q -p:WarningLevel=0 -clp:ErrorsOnly`

Test example:
`dotnet test source/SchedulePlanner.Core.Tests/SchedulePlanner.Core.Tests.csproj --no-build`

Run example (no need to build first):
`dotnet run --project source/SchedulePlanner.Cli/SchedulePlanner.Cli.csproj`