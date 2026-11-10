#!/bin/bash
# usage: bash PCWT_go.sh PCWT_L001 PRVEq_Module   (one Lean scope; runs from the evidence dir)
cd "$(dirname "$0")" && export PCWT_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p7a-20261110 && python3 -B PCWT_run.py "$1" lean "$2"
