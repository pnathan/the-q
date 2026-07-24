#!/bin/bash
# Script to run Verus verification on the Q type specifications
# This requires a Verus installation with Z3 4.12.5

set -e

# Check if Verus is available
if ! command -v vargo &> /dev/null; then
    echo "Error: vargo not found. Please install Verus first."
    echo "See VERIFICATION.md for Verus installation instructions."
    exit 1
fi

# Set Z3 path if not already set
if [ -z "$VERUS_Z3_PATH" ]; then
    if command -v z3 &> /dev/null; then
        export VERUS_Z3_PATH=$(which z3)
    else
        echo "Error: Z3 not found in PATH"
        echo "Set VERUS_Z3_PATH environment variable to Z3 executable"
        exit 1
    fi
fi

echo "Running Verus verification..."
echo "  VERUS_Z3_PATH=$VERUS_Z3_PATH"

# Run vargo to execute the verifier
vargo run -p rust_verify --release -- "$(cd "$(dirname "$0")/.." && pwd)/src/verus_verify.rs"

echo ""
echo "✓ Verus verification complete"
