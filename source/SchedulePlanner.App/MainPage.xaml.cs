namespace SchedulePlanner.App;

using SchedulePlanner.App.ViewModels;
using SchedulePlanner.Core;

public partial class MainPage : ContentPage
{
    private readonly MainViewModel _viewModel;

    public MainPage(MainViewModel viewModel, SchedulingService service)
    {
        InitializeComponent();
        viewModel.Strategy = service;
        BindingContext = _viewModel = viewModel;
    }

    protected override async void OnAppearing()
    {
        base.OnAppearing();
        await _viewModel.InitializeAsync();
    }
}