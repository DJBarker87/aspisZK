#!/bin/bash
# usage: bash run_ext.sh PCWP_E00N   (one extraction scope at a time)
cd "$(dirname "$0")"
python3 -B PCWP_run.py "$1" extract > "$1.client.log" 2>&1
echo "exit=$?" >> "$1.client.log"
rm -rf __pycache__
