#!/bin/bash
# usage: bash run1.sh LID BUNDLE
cd "$(dirname "$0")"
python3 -B PCUC_run.py "$1" lean "$2" > "run_$1.out" 2>&1
echo "exit $?" >> "run_$1.out"
