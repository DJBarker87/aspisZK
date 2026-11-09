#!/bin/bash
cd "$(dirname "$0")"
i=11
for b in F1 F2 F3 F4a F4b F5 F4d F4c; do
  a=$(printf "PCUE_L%03d" $i)
  bash run_scope.sh $a PRVEq_bundle_${b}1
  echo "$a $b $(tail -1 $a.client.log)" >> chain2.log
  i=$((i+1))
done
echo done >> chain2.log
