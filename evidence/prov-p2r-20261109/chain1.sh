#!/bin/bash
cd "$(dirname "$0")"
i=3
for b in T2 T3 T4 F1 F2 F3 F4 F5; do
  a=$(printf "PCUE_L%03d" $i)
  bash run_scope.sh $a PRVEq_bundle_${b}1
  echo "$a $b $(tail -1 $a.client.log)" >> chain1.log
  i=$((i+1))
done
echo done >> chain1.log
