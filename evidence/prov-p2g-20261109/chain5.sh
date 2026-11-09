#!/bin/bash
# verification compiles of the final generated files (round 2): V1 = D,T1,T2,A,W,P ; V2 = N1,N2,N3,N4a,N4d
cd "$(dirname "$0")"
i=21
for b in V1 V2; do
  a=$(printf "PCUG_L%03d" $i)
  bash run_scope.sh $a PRVEq_bundle_${b}2
  echo "$a $b $(tail -2 $a.client.log | tr '\n' ' ' | cut -c1-300)" >> chain5.log
  i=$((i+1))
done
echo done >> chain5.log
