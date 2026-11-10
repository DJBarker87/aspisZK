#!/bin/bash
cd "$(dirname "$0")"
i=6
for b in C02 C03 C04 C05 C06 C07 C08 C09 C10 C11 C12 C13; do
  a=$(printf "PCXB_L%03d" $i)
  bash run_scope.sh $a PRVCmb_$b
  echo "$a $b $(head -c 160 $a.client.log | head -1)" >> chain1.log
  i=$((i+1))
  if ! grep -q '"exit_status": 0' $a.client.log; then echo "STOP at $a $b" >> chain1.log; break; fi
done
echo done >> chain1.log
