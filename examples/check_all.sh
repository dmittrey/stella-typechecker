#!/bin/bash

BASE_DIR="$(dirname "$0")"
CHECK_SCRIPT="$BASE_DIR/check_dir.sh"

if [ ! -x "$CHECK_SCRIPT" ]; then
    echo "Ошибка: $CHECK_SCRIPT не найден или не исполнимый"
    exit 1
fi

grand_total=0
grand_mismatches=0

for dir in "$BASE_DIR"/*; do
    if [ -d "$dir" ]; then
        echo "=== Проверка директории: $dir ==="
        "$CHECK_SCRIPT" "$dir"
        mismatches=$?
        files_count=$(ls -1 "$dir" | wc -l)

        grand_total=$((grand_total+files_count))
        grand_mismatches=$((grand_mismatches+mismatches))

        echo
    fi
done

echo "=== Итоговый результат ==="
echo "Всего файлов   : $grand_total"
echo "Несовпадений   : $grand_mismatches"
