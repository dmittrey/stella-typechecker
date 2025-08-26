#!/bin/bash

# Проверяем, что передан аргумент
if [ -z "$1" ]; then
    echo "Использование: $0 <директория>"
    exit 1
fi

DIR="$1"

# Проверка существования директории
if [ ! -d "$DIR" ]; then
    echo "Ошибка: директория '$DIR' не существует"
    exit 1
fi

# Перебираем все файлы в директории
for file in "$DIR"/*; do
    if [ -f "$file" ]; then
        echo "=== Запуск для файла: $file ==="
        ../src/Stella/Main "$file"
        echo
    fi
done
