#!/bin/bash
# usage: bash run_scope.sh PCXC_L00N TARGET   (one scope at a time; TARGET.lean next to this script)
cd "$(dirname "$0")"
python3 -B PCXC_run.py "$1" lean "$2" > "$1.client.log" 2>&1
echo "exit=$?" >> "$1.client.log"
