using System.Diagnostics.CodeAnalysis;

namespace SchedulePlanner;

public static class ExtensionMethods
{
    public static bool IsNullOrEmpty<T>([NotNullWhen(false)] this ICollection<T> list) =>
        !(list?.Count > 0);

    public static bool IsNullOrEmpty<T>([NotNullWhen(false)] this IEnumerable<T> enumerable) =>
        !enumerable?.Any() ?? true;

    public static string ToEnumeratedString<T>(this IEnumerable<T> data, string div = ", ") =>
        data is null ? string.Empty : string.Join(div, data.Select(o => o?.ToString() ?? string.Empty));

    public static string ToDateTimeName(this DateTime dateTime, string prefix = "", string suffix = "") =>
        string.Format("{0}{1:yyyyMMdd_HHmmss}{2}", prefix, dateTime, suffix);
}
