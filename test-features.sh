#!/bin/bash
# Test script for Leo3 feature combinations
#
# This script tests Leo3 with different feature flag combinations
# to ensure compatibility across configurations.
#
# Inspired by PyO3's feature testing approach.

set -e

echo "=== Leo3 Feature Testing ==="
echo

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# Function to run tests with specific features
test_features() {
    local features=$1
    local description=$2

    echo "Testing: $description"
    echo "Features: $features"

    if [ -z "$features" ]; then
        cargo test --no-default-features --lib
    else
        cargo test --no-default-features --features "$features" --lib
    fi

    if [ $? -eq 0 ]; then
        echo -e "${GREEN}✓ Passed${NC}"
    else
        echo -e "${RED}✗ Failed${NC}"
        exit 1
    fi
    echo
}

# Test with no features
echo "--- Phase 1: Minimal Configuration ---"
test_features "" "No features (minimal)"

# Test with individual features
echo "--- Phase 2: Individual Features ---"
test_features "macros" "Macros only"

# Test with default features
echo "--- Phase 3: Default Configuration ---"
echo "Testing: Default features"
cargo test --lib

if [ $? -eq 0 ]; then
    echo -e "${GREEN}✓ Passed${NC}"
else
    echo -e "${RED}✗ Failed${NC}"
    exit 1
fi
echo

# Test all workspace crates
echo "--- Phase 4: Full Workspace ---"
echo "Testing: All workspace crates"
cargo test --workspace --lib

if [ $? -eq 0 ]; then
    echo -e "${GREEN}✓ Passed${NC}"
else
    echo -e "${RED}✗ Failed${NC}"
    exit 1
fi
echo

# Future: Test with different Lean4 versions
# echo "--- Phase 5: Lean4 Version Matrix ---"
# LEAN_VERSION=4.0 cargo test
# LEAN_VERSION=4.1 cargo test
# LEAN_VERSION=4.2 cargo test

echo "=== All Feature Tests Passed! ==="
