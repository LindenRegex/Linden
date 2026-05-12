#!/bin/bash

# viz.sh: Cleans Rocq output and renders it via Graphviz
# Usage: ./viz.sh your_output_file.dot.out

set -e

if [ ! -f "$1" ]; then
    echo "Usage: $0 <file_containing_rocq_output>"
    exit 1
fi

TMP_DIR=$(mktemp -d)
DOT_FILE="$TMP_DIR/tree.dot"
OUT_FILE="$TMP_DIR/tree.svg"

# 1. Remove the ' = "' prefix from the start
# 2. Replace all "" with "
# 3. Remove the trailing '"' and ': string' type info
sed -E \
    -e 's/^[[:space:]]*=[[:space:]]*"//' \
    -e 's/""/"/g' \
    -e 's/^}"[[:space:]]*$/}/' \
    -e 's/^[[:space:]]*:[[:space:]]*string[[:space:]]*$//' \
    "$1" > "$DOT_FILE"

# Check if Graphviz is installed
if ! command -v dot &> /dev/null; then
    echo "Error: 'dot' command not found. Install Graphviz to proceed."
    exit 1
fi

dot -Tsvg "$DOT_FILE" -o "$OUT_FILE"

# Open image
OS_NAME=$(uname -s)
if [ "$OS_NAME" = "Darwin" ]; then
    open "$OUT_FILE"
elif [ "$OS_NAME" = "Linux" ]; then
    xdg-open "$OUT_FILE"
else
    echo "Rendered to: $OUT_FILE"
fi

# Keep the temp dir path
echo "Files located in: $TMP_DIR"
