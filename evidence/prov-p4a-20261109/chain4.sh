#!/bin/bash
cd "$(dirname "$0")"
export PCWA_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p4a-20261109
for a in PCWA_E011 PCWA_E012; do
  python3 PCWA_run.py $a extract > $a.client.log 2>&1; echo "$a exit $?" >> chain4.log
done
