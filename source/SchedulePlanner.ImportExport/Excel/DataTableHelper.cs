using System.Data;
using System.Reflection;

internal static class DataTableHelper
{
    extension<T>(IEnumerable<T> list)
    {
        /// <summary>
        /// Converts an IEnumerable object to a data table of values.
        /// </summary>
        public DataTable CreateDataTable()
        {
            ArgumentNullException.ThrowIfNull(list);

            var type = typeof(T);
            var properties = type.GetProperties(BindingFlags.Public | BindingFlags.Instance);

            var dataTable = new DataTable
            {
                TableName = type.Name
            };

            foreach (var heading in properties)
            {
                var columnType = Nullable.GetUnderlyingType(heading.PropertyType) ?? heading.PropertyType;
                dataTable.Columns.Add(new DataColumn(heading.Name, columnType));
            }

            foreach (var entity in list)
            {
                var values = new object?[properties.Length];
                for (int i = 0; i < properties.Length; i++)
                {
                    values[i] = properties[i].GetValue(entity) ?? DBNull.Value;
                }

                dataTable.Rows.Add(values);
            }

            dataTable.AcceptChanges();
            return dataTable;
        }
    }

    public static DataTable CreateDataTable(
        this IEnumerable<DataRow> rows,
        IEnumerable<DataColumn>? headings = null)
    {
        var table = new DataTable();

        headings ??=
        [
            table.Columns.Add("Key", typeof(string)),
            table.Columns.Add("Value", typeof(object))
        ];

        foreach (var row in rows)
            table.Rows.Add(row);

        return table;
    }
}
