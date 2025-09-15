#!/bin/bash

if [ -z "$1" ]; then
    echo "Usage: $0 <directory>"
    exit 1
fi

DIR="$1"

if [ ! -d "$DIR" ]; then
    echo "Error: directory '$DIR' does not exist"
    exit 1
fi

total=0
mismatches=0

# Recursively find all .st files
while IFS= read -r file; do

    total=$((total+1))
    echo "=== Running test for file: $file ==="

    output=$(./src/Stella/Main "$file" 2>&1)
    normalized=$(echo "$output" | xargs)
    expected=$(tail -n 1 "$file" | sed 's#//##' | xargs)

    # Extract only the code: SUCCESS or ERROR_*
    if [[ "$normalized" == *"Type error:"* ]]; then
        actual_code=$(echo "$normalized" | sed -n 's/.*Type error: \([^ ]*\).*/\1/p')
    elif [[ "$normalized" == *"Type checking passed!"* ]]; then
        actual_code="SUCCESS"
    else
        actual_code="$normalized"
    fi

    echo "$output"

    if [[ "$expected" != "$actual_code" ]]; then
        mismatches=$((mismatches+1))
        echo "::error file=$file::Expected '$expected', got '$actual_code'"
    fi

    echo
done < <(find "$DIR" -type f)

echo "=== Directory check: $DIR ==="
echo "Total tests    : $total"
echo "Mismatches     : $mismatches"
echo "Tests passed   : $((total - mismatches))/$total"

exit $mismatches
