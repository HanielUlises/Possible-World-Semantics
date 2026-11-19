#!/usr/bin/env bash
set -e

echo "cleaning build artifacts..."
lake clean

echo "building and verifying..."
lake build

echo "checking the model against the axioms..."
python3 "$(dirname "$0")/check_model.py"

echo "done. all proofs verified."
