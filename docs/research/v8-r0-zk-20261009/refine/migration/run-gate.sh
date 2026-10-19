#!/bin/sh
# run-gate.sh <label> <source dir> <cargo target dir> <out dir> <command...>
# One gate step of the writer migration (LOG D68.2) on the build host, in its own
# capped scope (MemoryHigh 6G / MemoryMax 8G / swap 0 / 64 tasks), timed by
# /usr/bin/time -v.  Writes <out>/<label>.{stdout,stderr,time,exit,cmd}.
set -u
L=$1; S=$2; T=$3; O=$4; shift 4
mkdir -p "$O"
echo "$*" > "$O/$L.cmd"
cd "$S" || exit 2
systemd-run --user --scope --quiet --unit="r1p-wm-$L-$$" \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  --setenv=CARGO_TARGET_DIR="$T" --setenv=PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin \
  /usr/bin/time -v -o "$O/$L.time" timeout 3000 "$@" > "$O/$L.stdout" 2> "$O/$L.stderr"
rc=$?
echo "$rc" > "$O/$L.exit"
printf '%s exit=%s ' "$L" "$rc"; grep -hE "Elapsed|Maximum res" "$O/$L.time" | tr -s ' \t' ' ' | tr '\n' ' '; echo
exit $rc
