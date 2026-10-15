#!/usr/bin/env bash
set -u
ulimit -c 0
BASE=/home/dombarker/project-offloads/aspis-r1-wide-parser-extraction-next-20261015
INPUT=/home/dombarker/project-offloads/aspis-r1-wide-parser-input-20261015-e
OUT=$BASE/attempt-e
if [ -e "$OUT" ]; then
  echo "refusing existing attempt dir: $OUT" >&2
  exit 98
fi
if systemd-run --user --scope --quiet \
  -p MemoryHigh=4G -p MemoryMax=6G -p MemorySwapMax=0 -p TasksMax=128 \
  /usr/bin/time -v -o "$BASE/attempt-e.outer.time.log" \
  /usr/bin/timeout 900 python3 "$INPUT/extract-field-parsers.py" \
  --input "$INPUT" --output "$OUT" \
  --entry crate::parse_wide_exact_probe \
  --namespace AspisR1WideParser --mir built \
  > "$BASE/attempt-e.outer.log" 2>&1; then
  STATUS=0
else
  STATUS=$?
fi
printf '{"attempt":"e","exit":%s,"scope":{"MemoryHigh":"4G","MemoryMax":"6G","MemorySwapMax":"0","TasksMax":128},"mir":"built","monomorphize":false}\n' "$STATUS" > "$BASE/attempt-e.result.json"
cat "$BASE/attempt-e.result.json"
exit "$STATUS"
