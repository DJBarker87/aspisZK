#!/bin/bash
# round-1 probes of the shapes changed by PCUG change 2 (skip divergent loops); only bundles that still contain attempted theorems
cd "$(dirname "$0")"
i=20
for b in diag_N14p2; do
  a=$(printf "PCUG_L%03d" $i)
  bash run_scope.sh $a PRVEq_${b}
  echo "$a $b $(tail -2 $a.client.log | tr '\n' ' ' | cut -c1-300)" >> chain4.log
  i=$((i+1))
done
echo done >> chain4.log
