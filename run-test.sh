#!/bin/zsh
# Run a single Koka test file using the dev-compiler version of Koka (via ./koka)

if [[ -z "$1" ]]; then
  echo "Usage: run-test.sh <test-file.kk>"
  echo "Example: run-test.sh test/common/name.kk"
  exit 1
fi

TEST_FILE="$1"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if [[ ! -f "$SCRIPT_DIR/$TEST_FILE" ]]; then
  echo "Error: Test file not found: $SCRIPT_DIR/$TEST_FILE"
  exit 1
fi

# Run the test from the compiler directory with relative paths
cd "$SCRIPT_DIR"
echo " + Running $TEST_FILE..."
"$SCRIPT_DIR/koka" -e "$TEST_FILE"
