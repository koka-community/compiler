#!/bin/zsh
# Run a single Koka test file using the dev version of Koka

if [[ -z "$1" ]]; then
  echo "Usage: run-test.sh <test-file.kk>"
  echo "Example: run-test.sh test/common/name.kk"
  exit 1
fi

TEST_FILE="$1"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
KOKA_DEV_DIR=~/koka

if [[ ! -f "$SCRIPT_DIR/$TEST_FILE" ]]; then
  echo "Error: Test file not found: $SCRIPT_DIR/$TEST_FILE"
  exit 1
fi

# Find the koka executable using stack
KOKA_BIN=$(cd "$KOKA_DEV_DIR" && stack exec which koka 2>/dev/null)

if [[ -z "$KOKA_BIN" ]] || [[ ! -f "$KOKA_BIN" ]]; then
  echo "Error: Could not find koka executable"
  exit 1
fi

# Run the test from the compiler directory with relative paths
cd "$SCRIPT_DIR"
echo " + Running $TEST_FILE..."
"$KOKA_BIN" -e -i../std -i. "$TEST_FILE"




