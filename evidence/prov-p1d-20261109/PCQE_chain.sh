#!/bin/bash
# usage: bash PCQE_chain.sh E001 E002 ...  strictly sequential, one scope at a time
export PCQE_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p1d-20261109
cd "$(dirname "$0")"
for n in "$@"; do
  timeout 900 python3 -B PCQE_run.py PCQE_$n extract > PCQE_$n.client.log 2>&1
  echo "PCQE_$n rc=$?" >> PCQE_chain.log
  git add --sparse . && git commit -qm "Stream C provenance P1d (PCQE_): PCQE_$n"
done
