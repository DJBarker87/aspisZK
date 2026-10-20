#!/usr/bin/env bash
# Execute within a caller-created capped systemd scope. Never opens task keys.
set -euo pipefail
[[ $# -ge 4 ]] || { echo 'usage: receipt.sh NEW_RUN_DIR SOURCE_REVISION EXPECTATION COMMAND [ARGS...]' >&2; exit 2; }
out=$1 revision=$2 expectation=$3
shift 3
[[ ! -e $out ]] || { echo "refusing receipt overwrite: $out" >&2; exit 2; }
mkdir -p "$out"
date -u +%FT%TZ >"$out/started-utc.txt"
printf '%s\n' "$revision" >"$out/source-revision.txt"
printf '%s\n' "$expectation" >"$out/expectation.txt"
printf '%q ' "$@" >"$out/command.txt"
printf '\n' >>"$out/command.txt"
cat /proc/self/cgroup >"$out/cgroup.txt"
cg=$(awk -F: '$1 == "0" {print $3}' /proc/self/cgroup)
for prop in memory.high memory.max memory.swap.max pids.max; do
  cat "/sys/fs/cgroup$cg/$prop" >"$out/$prop"
done
[[ $(cat "$out/memory.high") == 6442450944 &&
   $(cat "$out/memory.max") == 8589934592 &&
   $(cat "$out/memory.swap.max") == 0 &&
   $(cat "$out/pids.max") == 64 ]] || exit 2
export RUSTFLAGS='-C link-arg=-Wl,--threads=4'
printf '%s\n' "$RUSTFLAGS" >"$out/RUSTFLAGS.txt"
status=0
/usr/bin/time -v -o "$out/time.txt" "$@" >"$out/stdout.txt" 2>"$out/stderr.txt" || status=$?
printf '%s\n' "$status" >"$out/exit.txt"
cat "/sys/fs/cgroup$cg/memory.peak" >"$out/memory.peak"
printf '%s\n' 'N/A (no Lean)' >"$out/print-axioms.txt"
date -u +%FT%TZ >"$out/finished-utc.txt"
exit "$status"
