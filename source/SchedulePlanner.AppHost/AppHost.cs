var builder = DistributedApplication.CreateBuilder(args);

builder.AddProject<Projects.SchedulePlanner_App>("scheduleplanner-app");

builder.Build().Run();
