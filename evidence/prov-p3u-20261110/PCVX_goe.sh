#!/bin/bash
# usage: bash PCVX_goe.sh PCVX_Ennn   (one extraction scope)
cd "$(dirname "$0")"
python3 -B PCVX_run.py $1 extract > $1.client.log 2>&1
tail -c 700 $1.client.log
rm -rf __pycache__
