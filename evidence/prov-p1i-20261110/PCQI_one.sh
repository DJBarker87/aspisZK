#!/bin/bash
# usage: bash PCQI_one.sh L0NN TARGET : run one Lean scope and print the summary line + first errors
cd "$(dirname "$0")"
bash run_scope.sh PCQI_$1 $2
head -1 PCQI_$1.client.log | cut -c1-110
xz -dc PCQI_$1/stdout.log.xz 2>/dev/null | grep "error" -A8 | head -${3:-24}
