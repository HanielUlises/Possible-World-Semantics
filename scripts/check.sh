#!/usr/bin/env bash
set -e

echo "cleaning build artifacts..."
lake clean

echo "building and verifying (warnings, including sorry, are errors)..."
lake build --wfail

echo "done. all proofs verified."
