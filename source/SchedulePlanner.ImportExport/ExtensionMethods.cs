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

    public static string GetName<T>(this T item) where T : Enum =>
        item is null ? string.Empty : Enum.GetName(typeof(T), item) ?? string.Empty;

    public static TOut ChangeTypeTo<TOut>(this object value) where TOut : class, new() =>
        (Convert.ChangeType(value, typeof(TOut)) as TOut) ?? new TOut();
}
