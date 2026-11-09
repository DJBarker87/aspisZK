#!/bin/bash
# usage: bash PCQC_chain2.sh NEWRUN ... (specs already rendered); strictly sequential
export PCQC_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p1c-20261109
cd "$(dirname "$0")"
for new in "$@"; do
  timeout 900 python3 -B PCQC_run.py "$new" extract > "$new.client.log" 2>&1
  echo "$new rc=$?" >> PCQC_chain.log
  git add --sparse . && git commit -qm "Stream C provenance P1c (PCQC_): $new"
done
