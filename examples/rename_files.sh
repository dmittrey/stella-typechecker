#!/bin/bash

BASE_DIR="$1"

if [ -z "$BASE_DIR" ]; then
    echo "Использование: $0 <директория>"
    exit 1
fi

if [ ! -d "$BASE_DIR" ]; then
    echo "Ошибка: директория '$BASE_DIR' не существует"
    exit 1
fi

# Проходим рекурсивно по всем поддиректориям
find "$BASE_DIR" -type f -name "*.st" | while read -r file; do
    dir_name=$(basename "$(dirname "$file")")
    
    # Проверяем последнюю строку
    last_line=$(tail -n 1 "$file")
    if [[ "$last_line" == "//"* ]]; then
        # заменяем последнюю строку на //dirname
        sed -i '' -e "\$s#.*#//$dir_name#" "$file"
    else
        # добавляем //dirname в конец файла
        echo "/n/n//$dir_name" >> "$file"
    fi

    echo "Обработан файл: $file -> //$dir_name"
done
