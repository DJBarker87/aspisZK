#!/bin/bash
# usage: bash run_scope.sh PCXH_L00N MOD1[,MOD2,...]   (one scope at a time; MODi.lean next to this script)
cd "$(dirname "$0")"
python3 -B PCXH_run.py "$1" "$2" > "$1.client.log" 2>&1
echo "exit=$?" >> "$1.client.log"
