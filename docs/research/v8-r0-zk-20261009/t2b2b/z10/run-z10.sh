#!/bin/sh
# Z10 runner: build optimized, run every configuration, keep per-job time -v receipts.
# Launched by the caller inside: systemd-run --user --scope -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 -p TasksMax=64
set -u
D=$(cd "$(dirname "$0")" && pwd); OUT=${1:-$D/runs}; mkdir -p "$OUT"
cd "$D" && cargo build --release > "$OUT/build.log" 2>&1 || { echo BUILD_FAIL; exit 1; }
B=$D/target/release/z10
sha256sum main.rs Cargo.toml run-z10.sh > "$OUT/source-sha256.txt"
run() { name=$1; shift; /usr/bin/time -v -o "$OUT/$name.time" "$B" "$@" > "$OUT/$name.log" 2> "$OUT/$name.err"; echo "$name exit=$?" >> "$OUT/exits.txt"; }
# main grid: lane shape x transport x query structure (seed fixed per job)
for e in 21 7 1 26 0; do for pi in id rand; do
  run "e${e}-${pi}-uniform" $e $pi 1000 uniform 11 &
  run "e${e}-${pi}-coset" $e $pi 150 coset 12 &
  run "e${e}-${pi}-consecutive" $e $pi 150 consecutive 13 &
  wait
done; done
# sensitivity controls: margin pushed to 0 and to -1 by generic padding (e = 21, id)
run "ctl-margin0" 21 id 100 uniform 21 531 &
run "ctl-margin-1" 21 id 20 uniform 22 532 &
# Route M2 residual certificate shape (identity transport, indicative) and its control
run "kron" kron 200 31 &
run "kron-control" kron 20 32 control &
wait
echo DONE >> "$OUT/exits.txt"
