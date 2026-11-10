#!/bin/bash
# usage: bash PCUI_chain.sh LISTFILE START LOG   one scope at a time; stops only on transport/admission errors
cd "$(dirname "$0")"
i=$2
while read t; do
  a=$(printf "PCUI_L%03d" $i)
  bash run_scope.sh $a $t < /dev/null
  echo "$a $t $(head -c 120 $a.client.log | head -1)" >> $3
  i=$((i+1))
done < $1
echo done >> $3
