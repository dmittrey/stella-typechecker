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

for file in "$DIR"/*; do
    if [ -f "$file" ]; then
        echo "=== Запуск для файла: $file ==="

        output=$(../src/Stella/Main "$file")

        # ожидаемая ошибка из комментария
        expected=$(tail -n 1 "$file" | sed 's#//##' | xargs)

        # нормализованный вывод
        normalized=$(echo "$output" | xargs)

        # если ошибка, берём только код (первые два токена "Type error:" и сам код)
        if [[ "$normalized" == Type\ error:* ]]; then
            actual_code=$(echo "$normalized" | cut -d' ' -f3)
        else
            actual_code="$normalized"
        fi

        echo "$output"

        if [[ "$expected" == "SUCCESS" && "$normalized" == "Type checking passed!" ]]; then
            echo "✅ Совпало: SUCCESS"
        elif [[ "$normalized" == Type\ error:* && "$expected" == "$actual_code" ]]; then
            echo "✅ Совпало: $expected"
        else
            echo "❌ Несовпадение!"
            echo "   Ожидалось: $expected"
            echo "   Получено : $normalized"
        fi

        echo
    fi
done
