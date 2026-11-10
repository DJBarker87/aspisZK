#!/bin/bash
# usage: bash PCWN_chain.sh L005:PRVEq_X L006:PRVEq_Y ...  (serial, one scope at a time)
cd "$(dirname "$0")"
for p in "$@"; do a=PCWN_${p%%:*}; t=${p#*:}; python3 -B PCWN_run.py $a lean $t > $a.out 2>&1; echo "$a $t rc=$?" >> PCWN_chain.log; done
