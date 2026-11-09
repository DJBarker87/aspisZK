#!/bin/bash
# usage: bash PCQD_chain.sh RUN:SPEC[:NOTE] ...  strictly sequential (one scope at a time)
export PCQD_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p1g-20261109
cd "$(dirname "$0")"
for x in "$@"; do
  IFS=: read run spec note <<< "$x"
  python3 -B PCQD_render_spec.py "$spec" "$run" "$note" >/dev/null || { echo "$run SPECFAIL" >> PCQD_chain.log; continue; }
  timeout 1500 python3 -B PCQD_run.py "$run" extract > "$run.client.log" 2>&1
  echo "$run $spec rc=$?" >> PCQD_chain.log
done
