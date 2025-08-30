#!/bin/bash

# Путь к директории, где лежит этот скрипт
BASE_DIR="$(dirname "$0")"

# Скрипт проверки
CHECK_SCRIPT="$BASE_DIR/check_dir.sh"

# Проверяем, что скрипт существует и исполнимый
if [ ! -x "$CHECK_SCRIPT" ]; then
    echo "Ошибка: $CHECK_SCRIPT не найден или не исполнимый"
    exit 1
fi

# Обходим все поддиректории
for dir in "$BASE_DIR"/*; do
    if [ -d "$dir" ]; then
        echo "=== Проверка директории: $dir ==="
        "$CHECK_SCRIPT" "$dir"
        echo
    fi
done
