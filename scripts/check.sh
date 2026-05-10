#!/usr/bin/env bash
set -e

echo "cleaning build artifacts..."
lake clean

echo "building and verifying..."
lake build

echo "done. all proofs verified."