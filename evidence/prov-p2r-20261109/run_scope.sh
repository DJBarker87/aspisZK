#!/bin/bash
# usage: bash run_scope.sh PCUE_L00N BUNDLE   (run from this directory)
cd "$(dirname "$0")"
python3 -B PCUE_run.py "$1" lean "$2" > "$1.client.log" 2>&1
echo "exit=$?" >> "$1.client.log"
