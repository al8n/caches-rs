#!/bin/bash
set -e

rustup toolchain install nightly --component miri
rustup override set nightly
cargo miri setup

export MIRIFLAGS="-Zmiri-disable-isolation -Zmiri-symbolic-alignment-check"

cargo miri test

