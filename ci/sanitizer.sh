#!/bin/bash

set -ex

# export ASAN_OPTIONS="detect_odr_violation=0 detect_leaks=0"

# Run address sanitizer
RUSTFLAGS="--cfg all_skl_tests -Z sanitizer=address" \
cargo test --lib --all-features --target x86_64-unknown-linux-gnu

# # Run leak sanitizer
# RUSTFLAGS="--cfg all_skl_tests -Zsanitizer=leak" \
# cargo test -Zbuild-std --release --tests --target x86_64-unknown-linux-gnu --features memmap

# Run memory sanitizer
RUSTFLAGS="--cfg all_skl_tests -Zsanitizer=memory -Zsanitizer-memory-track-origins" \
RUSTDOCFLAGS="-Zsanitizer=memory -Zsanitizer-memory-track-origins" \
cargo test -Zbuild-std --release --tests --target x86_64-unknown-linux-gnu --features memmap

# Run thread sanitizer
RUSTFLAGS="--cfg all_skl_tests -Z sanitizer=thread" \
cargo -Zbuild-std test --lib --target x86_64-unknown-linux-gnu --features memmap