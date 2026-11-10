#!/bin/bash
# NPE_ Rust semantics test: run inside a capped user scope.
set -u
cd "$(dirname "$0")"
export PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin
for TC in nightly-2026-09-17 1.94.1; do
  echo "=== toolchain $TC: $(rustup run $TC rustc --version)"
  for OC in on off; do
    for OPT in 0 3; do
      out=bin_${TC}_oc${OC}_O${OPT}
      rustup run $TC rustc --edition 2021 -C overflow-checks=$OC -C opt-level=$OPT -C debug-assertions=$( [ $OC = on ] && echo on || echo off ) -o $out NPE_shift_test.rs || { echo "COMPILE FAIL $out"; continue; }
      echo "--- $out"; ./$out; echo "exit=$?"
    done
    rustup run $TC rustc --edition 2021 -C overflow-checks=$OC -C opt-level=0 --emit=mir -o mir_${TC}_oc${OC}.mir NPE_shift_test.rs
  done
done
