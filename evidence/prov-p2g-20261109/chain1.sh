#!/bin/bash
cd "$(dirname "$0")"
i=1
for b in D T1 T2 A W P N1 N2 N3 N4 N5; do
  a=$(printf "PCUG_L%03d" $i)
  bash run_scope.sh $a PRVEq_bundle_${b}1
  echo "$a $b $(tail -2 $a.client.log | tr '\n' ' ' | cut -c1-300)" >> chain1.log
  i=$((i+1))
done
echo done >> chain1.log
