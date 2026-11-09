#!/bin/bash
# round-1 probes of the shapes changed by PCUG change 2 (skip divergent loops); only bundles that still contain attempted theorems
cd "$(dirname "$0")"
i=18
for b in N4d N5b; do
  a=$(printf "PCUG_L%03d" $i)
  bash run_scope.sh $a PRVEq_bundle_${b}1
  echo "$a $b $(tail -2 $a.client.log | tr '\n' ' ' | cut -c1-300)" >> chain3.log
  i=$((i+1))
done
echo done >> chain3.log
