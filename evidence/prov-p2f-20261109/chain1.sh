#!/bin/bash
cd "$(dirname "$0")"
i=2
for b in B11 B21 B31 B41 B51 B61 H41 H11 H21 H31; do
  a=$(printf "PCUF_L%03d" $i)
  bash run_scope.sh $a PRVEq_bundle_$b
  echo "$a $b $(tail -1 $a.client.log | cut -c1-300)" >> chain1.log
  i=$((i+1))
done
echo done >> chain1.log
