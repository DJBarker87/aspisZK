#!/bin/bash
cd "$(dirname "$0")"
export PCWA_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p4a-20261109
for r in PCWA_E002:x PCWA_E003:x PCWA_E004:x PCWA_E005:x PCWA_E006:x; do
  a=${r%%:*}; python3 PCWA_run.py $a extract > $a.client.log 2>&1; echo "$a exit $?" >> chain1.log
done
