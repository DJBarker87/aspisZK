#!/bin/bash
cd "$(dirname "$0")"
export PCWA_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p4a-20261109
python3 PCWA_run.py PCWA_L005 lean PRVEq_bundle_A1 > PCWA_L005.client.log 2>&1; echo "L005 $?" >> chain7.log
python3 PCWA_run.py PCWA_L006 lean PRVEq_bundle_B1 > PCWA_L006.client.log 2>&1; echo "L006 $?" >> chain7.log
python3 PCWA_run.py PCWA_L007 lean PRVEq_bundle_C1 > PCWA_L007.client.log 2>&1; echo "L007 $?" >> chain7.log
python3 PCWA_run.py PCWA_L008 lean PRVEq_bundle_C2 > PCWA_L008.client.log 2>&1; echo "L008 $?" >> chain7.log
