#!/bin/bash
cd "$(dirname "$0")"
i=20
for b in VT1 VT2 VF1 VF2 VF3 VF4; do
  a=$(printf "PCUE_L%03d" $i)
  bash run_scope.sh $a PRVEq_bundle_${b}2
  echo "$a $b $(tail -1 $a.client.log)" >> chain3.log
  i=$((i+1))
done
echo done >> chain3.log
