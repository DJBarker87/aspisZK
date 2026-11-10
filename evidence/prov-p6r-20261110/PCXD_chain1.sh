#!/bin/bash
cd "$(dirname "$0")"
i=2
for b in C15 C16 C17; do
  a=$(printf "PCXD_L%03d" $i)
  bash run_scope.sh $a PRVCmb_$b
  echo "$a $b $(head -c 160 $a.client.log | head -1)" >> chain1.log
  i=$((i+1))
  if ! grep -q '"exit_status": 0' $a.client.log; then echo "STOP at $a $b" >> chain1.log; break; fi
done
echo done >> chain1.log
