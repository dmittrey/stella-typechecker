#!/bin/bash

if [ -z "$1" ]; then
    echo "Использование: $0 <директория>"
    exit 1
fi

DIR="$1"

if [ ! -d "$DIR" ]; then
    echo "Ошибка: директория '$DIR' не существует"
    exit 1
fi

total=0
mismatches=0

for file in "$DIR"/*; do
    if [ -f "$file" ]; then
        total=$((total+1))
        echo "=== Запуск для файла: $file ==="

        output=$(../src/Stella/Main "$file")

        expected=$(tail -n 1 "$file" | sed 's#//##' | xargs)
        normalized=$(echo "$output" | xargs)

        if [[ "$normalized" == Type\ error:* ]]; then
            actual_code=$(echo "$normalized" | cut -d' ' -f3)
        else
            actual_code="$normalized"
        fi

        echo "$output"

        if [[ "$expected" == "SUCCESS" && "$normalized" == "Type checking passed!" ]]; then
            continue
        elif [[ "$normalized" == Type\ error:* && "$expected" == "$actual_code" ]]; then
            continue
        else
            mismatches=$((mismatches+1))
            echo "❌ Несовпадение!"
            echo "   Ожидалось: $expected"
            echo "   Получено : $normalized"
        fi

        echo
    fi
done

echo "=== Результат проверки директории $DIR ==="
echo "Всего файлов   : $total"
echo "Несовпадений   : $mismatches"

# возвращаем количество несовпадений как exit code для check_all.sh
exit $mismatches
