#!/usr/bin/env bash
set -u
ulimit -c 0
BASE=/home/dombarker/project-offloads/aspis-r1-wide-parser-inline-extraction-20261015
INPUT=/home/dombarker/project-offloads/aspis-r1-wide-parser-inline-input-20261015
OUT=$BASE/attempt-g
if [ -e "$OUT" ]; then
  echo "refusing existing attempt dir: $OUT" >&2
  exit 98
fi
if systemd-run --user --scope --quiet \
  -p MemoryHigh=4G -p MemoryMax=6G -p MemorySwapMax=0 -p TasksMax=128 \
  /usr/bin/time -v -o "$BASE/attempt-g.outer.time.log" \
  /usr/bin/timeout 900 python3 "$INPUT/extract-field-parsers.py" \
  --input "$INPUT" --output "$OUT" \
  --entry crate::parse_wide_exact_probe \
  --namespace AspisR1WideParser --mir built \
  > "$BASE/attempt-g.outer.log" 2>&1; then
  STATUS=0
else
  STATUS=$?
fi
printf '{"attempt":"g","exit":%s,"scope":{"MemoryHigh":"4G","MemoryMax":"6G","MemorySwapMax":"0","TasksMax":128},"mir":"built","monomorphize":false}\n' "$STATUS" > "$BASE/attempt-g.result.json"
cat "$BASE/attempt-g.result.json"
exit "$STATUS"
