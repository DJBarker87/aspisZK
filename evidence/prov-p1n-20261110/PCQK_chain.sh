#!/bin/bash
# usage: bash PCQK_chain.sh LISTFILE START LOG : one Lean scope at a time (copy of PCUJ_chain.sh)
cd "$(dirname "$0")"
i=$2
while read t; do
  a=$(printf "PCQK_L%03d" $i)
  bash run_scope.sh $a $t < /dev/null
  echo "$a $t $(tail -2 $a.client.log | head -1 | cut -c1-160)" >> $3
  i=$((i+1))
done < $1
echo done >> $3
