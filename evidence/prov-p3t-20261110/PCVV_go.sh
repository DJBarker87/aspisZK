#!/bin/bash
# usage: bash PCVV_go.sh PCVV_Lnnn PRVEq_module   (runs one Lean scope in the background-safe way, prints errors)
cd "$(dirname "$0")"
python3 -B PCVV_run.py $1 lean $2 > $1.client.log 2>&1
tail -c 600 $1.client.log | head -c 600
echo
xz -dc $1/stdout.log.xz 2>/dev/null | grep -E 'error' | cut -c1-300 | head -${3:-25}
rm -rf __pycache__
