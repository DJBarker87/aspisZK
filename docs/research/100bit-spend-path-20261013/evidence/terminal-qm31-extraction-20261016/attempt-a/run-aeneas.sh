#!/usr/bin/env bash
set -uo pipefail
BASE=/home/dombarker/project-offloads/aspis-r1-terminal-extraction-20261016
ATT="$BASE/attempt-a"
LLBC="$ATT/output/charon-a/Terminal.llbc"
OUT="$ATT/output/aeneas-a"
mkdir -p "$OUT" "$ATT/receipts/aeneas-a"
AENEAS=/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/bin/aeneas
O="$ATT/receipts/aeneas-a"
test -s "$LLBC" || { echo missing-llbc >&2; exit 90; }
sha256sum "$LLBC" "$AENEAS" > "$O/input-tools.sha256"
"$AENEAS" -version > "$O/aeneas-version.txt" 2>&1
start=$(date -u +%Y-%m-%dT%H:%M:%SZ); t0=$(date +%s%N)
CG=$(cut -d: -f3 /proc/self/cgroup); CGROOT=/sys/fs/cgroup$CG
printf 'start=%s\ncgroup=%s\ncommand=%s -sequential -no-progress-bar -abort-on-error -print-unknown-externals -backend lean -namespace AspisR1TerminalProbe -dest %s -subdir AspisR1TerminalProbe -split-files -emit-json %s\n' "$start" "$CGROOT" "$AENEAS" "$OUT/generated" "$LLBC" > "$O/metadata.txt"
/usr/bin/time -v timeout 300s "$AENEAS" -sequential -no-progress-bar -abort-on-error -print-unknown-externals -backend lean -namespace AspisR1TerminalProbe -dest "$OUT/generated" -subdir AspisR1TerminalProbe -split-files -emit-json "$LLBC" > "$O/command.log" 2>&1
rc=$?
t1=$(date +%s%N); end=$(date -u +%Y-%m-%dT%H:%M:%SZ)
python3 - "$t0" "$t1" "$O/metadata.txt" "$rc" "$end" <<'PY'
import sys
s,e,path,rc,end=sys.argv[1:]
with open(path,"a") as f:f.write(f"exit={rc}\nend={end}\nwall_seconds={(int(e)-int(s))/1e9:.3f}\n")
PY
[ -r "$CGROOT/memory.peak" ] && cat "$CGROOT/memory.peak" > "$O/memory.peak" || true
[ -r "$CGROOT/memory.swap.current" ] && cat "$CGROOT/memory.swap.current" > "$O/memory.swap.current" || true
[ -r "$CGROOT/memory.events" ] && cat "$CGROOT/memory.events" > "$O/memory.events" || true
find "$OUT/generated" -maxdepth 4 -type f -print 2>/dev/null | sort > "$O/generated-files.txt"
while IFS= read -r f; do [ -f "$f" ] && sha256sum "$f"; done < "$O/generated-files.txt" > "$O/generated-sha256.txt"
exit "$rc"
