#!/bin/bash

set -ex

export ASAN_OPTIONS="detect_odr_violation=0 detect_leaks=0"

# Run leak sanitizer
RUSTFLAGS="-Z sanitizer=leak" \
cargo test --lib
