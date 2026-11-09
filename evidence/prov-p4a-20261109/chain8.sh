#!/bin/bash
cd "$(dirname "$0")"
export PCWA_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p4a-20261109
python3 PCWA_run.py PCWA_L009 lean PRVEq_bundle_VA > PCWA_L009.client.log 2>&1; echo "L009 $?" >> chain8.log
python3 PCWA_run.py PCWA_L010 lean PRVEq_bundle_VB > PCWA_L010.client.log 2>&1; echo "L010 $?" >> chain8.log
python3 PCWA_run.py PCWA_L011 lean PRVEq_bundle_VC > PCWA_L011.client.log 2>&1; echo "L011 $?" >> chain8.log
