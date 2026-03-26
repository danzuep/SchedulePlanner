using System.Data;

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
            var properties = type.GetProperties();

            var dataTable = new DataTable
            {
                TableName = type.Name
            };

            foreach (var heading in properties)
            {
                dataTable.Columns.Add(
                    new DataColumn(heading.Name.Replace('_', ' '),
                        Nullable.GetUnderlyingType(heading.PropertyType)
                        ?? heading.PropertyType));
            }

            foreach (T entity in list)
            {
                object?[] values = new object[properties.Length];
                for (int i = 0; i < properties.Length; i++)
                {
                    values[i] = properties[i].GetValue(entity);
                }
                dataTable.Rows.Add(values);
            }

            dataTable.AcceptChanges();
            return dataTable;
        }
    }
}
