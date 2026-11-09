#!/bin/bash
# usage: bash PCQC_chain.sh NEWRUN:OLDSPEC:OLDRUN:KIND ...   (strictly sequential: one scope at a time)
export PCQC_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p1c-20261109
cd "$(dirname "$0")"
for x in "$@"; do
  IFS=: read new oldspec oldrun kind <<< "$x"
  python3 -B PCQC_make_spec.py "$oldspec" "$oldrun" "$new" "$kind" >/dev/null || { echo "$new SPECFAIL" >> PCQC_chain.log; continue; }
  timeout 900 python3 -B PCQC_run.py "$new" extract > "$new.client.log" 2>&1
  echo "$new $oldrun $kind rc=$?" >> PCQC_chain.log
done
