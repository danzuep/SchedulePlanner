using System;
using System.Globalization;
using System.Windows.Data;

namespace SchedulePlanner.Wpf.Helpers;

public sealed class NotBooleanConverter : IValueConverter
{
    public object Convert(object? value, Type targetType, object? parameter, CultureInfo culture)
    {
        return value is false;
    }

    public object ConvertBack(object? value, Type targetType, object? parameter, CultureInfo culture)
    {
        return value is false;
    }
}
