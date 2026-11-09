#!/bin/bash
cd "$(dirname "$0")"
export PCWA_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p4a-20261109
python3 PCWA_run.py PCWA_L001 lean PRVEq_bundle_A1 > PCWA_L001.client.log 2>&1; echo "L001 $?" >> chain5.log
