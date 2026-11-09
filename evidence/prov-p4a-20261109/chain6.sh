#!/bin/bash
cd "$(dirname "$0")"
export PCWA_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p4a-20261109
python3 PCWA_run.py PCWA_L002 lean PRVEq_bundle_A1 > PCWA_L002.client.log 2>&1; echo "L002 $?" >> chain6.log
python3 PCWA_run.py PCWA_L003 lean PRVEq_bundle_B1 > PCWA_L003.client.log 2>&1; echo "L003 $?" >> chain6.log
python3 PCWA_run.py PCWA_L004 lean PRVEq_bundle_C1 > PCWA_L004.client.log 2>&1; echo "L004 $?" >> chain6.log
