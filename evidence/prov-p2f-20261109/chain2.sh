#!/bin/bash
cd "$(dirname "$0")"
i=15
for b in PRVEq_TD_HP_P3f PRVEq_bundle_V12 PRVEq_bundle_V22 PRVEq_bundle_V32 PRVEq_bundle_VH12 PRVEq_bundle_VH22 PRVEq_bundle_VH32 PRVEq_bundle_VX2 PRVEq_bundle_VY2; do
  a=$(printf "PCUF_L%03d" $i)
  bash run_scope.sh $a $b
  echo "$a $b $(tail -1 $a.client.log | cut -c1-100)" >> chain2.log
  i=$((i+1))
done
echo done >> chain2.log
