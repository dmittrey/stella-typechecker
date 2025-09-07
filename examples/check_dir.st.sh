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

mismatches=0
total=0

# Используем процесс подстановки вместо пайпа, чтобы цикл выполнялся в той же оболочке
while IFS= read -r file; do
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

    total=$((total+1))

    if [[ "$expected" == "SUCCESS" && "$normalized" == "Type checking passed!" ]]; then
        :
    elif [[ "$normalized" == Type\ error:* && "$expected" == "$actual_code" ]]; then
        :
    else
        mismatches=$((mismatches+1))
        echo "❌ Несовпадение!"
        echo "   Ожидалось: $expected"
        echo "   Получено : $normalized"
    fi

    echo
done < <(find "$DIR" -type f -name "*.st")

echo "=== Результат проверки ==="
echo "Всего файлов: $total"
echo "Несовпадений: $mismatches"
