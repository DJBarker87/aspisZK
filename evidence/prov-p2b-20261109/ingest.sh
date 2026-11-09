#!/bin/bash
# usage: ingest.sh BUNDLE PREV_ROUND ROUND LOG  (modules/args come from jobs.tsv: label module tag freshdir freshns [extra...])
cd "$(dirname "$0")"
bk=$1; prev=$2; rnd=$3; log=$4
while IFS='|' read -r label module tag fdir fns gate gtypes extra; do
  [ -z "$label" ] && continue
  grep -q "^PRVEq_$label\b" <(python3 -c "import json;print('\n'.join(json.load(open('gen/bundle_$bk${prev}_offsets.json'))))") || continue
  args=(--partition PCUB_PARTITION.json --module "$module" --fresh-dir "$fdir" --fresh-ns "$fns" --gate-source "$gate" --out "PRVEq_$label.lean" --report "gen/$label.report$rnd.json" --state "gen/$label.state$prev.json" --state-out "gen/$label.state$rnd.json" --lean-log "$log" --bundle-offsets "gen/bundle_$bk${prev}_offsets.json")
  [ -n "$tag" ] && args+=(--tag="$tag")
  [ -n "$gtypes" ] && args+=(--gate-types-source "$gtypes")
  [ -n "$extra" ] && args+=($extra)
  echo "== $label"; python3 -B PCUB_gen_equalities.py "${args[@]}" 2>&1 | tail -2
done < jobs.tsv
