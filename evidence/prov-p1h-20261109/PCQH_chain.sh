#!/bin/bash
# usage: bash PCQH_chain.sh RUN:SPEC ...  strictly sequential (one scope at a time)
export PCQH_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p1h-20261109
cd "$(dirname "$0")"
for x in "$@"; do
  IFS=: read run spec note <<< "$x"
  python3 -B PCQH_render_spec.py "$spec" "$run" "$note" >/dev/null || { echo "$run SPECFAIL" >> PCQH_chain.log; continue; }
  timeout 1500 python3 -B PCQH_run.py "$run" extract > "$run.client.log" 2>&1
  echo "$run $spec rc=$?" >> PCQH_chain.log
done
