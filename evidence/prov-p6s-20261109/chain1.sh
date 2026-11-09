#!/bin/bash
cd "$(dirname "$0")"
i=2
for b in A2 A3 A4 A5 A6 A7 A8; do
  a=$(printf "PCXA_L%03d" $i)
  bash run_scope.sh $a PRVEq_bundle_$b
  echo "$a $b $(tail -2 $a.client.log | head -1 | cut -c1-200)" >> chain1.log
  i=$((i+1))
  if ! grep -q '"exit_status": 0' $a.client.log; then echo "STOP at $a" >> chain1.log; break; fi
done
echo done >> chain1.log
