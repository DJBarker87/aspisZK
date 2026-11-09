#!/bin/bash
# re-probe of the P2b-origin bundles after PCUG-1 (rename of crate path prefixes); L012.. ; stops at the first timeout (exit 124) so a timed-out shape is not repeated
cd "$(dirname "$0")"
i=12
for b in N1 N2 N3 N4a N4b N5; do
  a=$(printf "PCUG_L%03d" $i)
  bash run_scope.sh $a PRVEq_bundle_${b}1
  echo "$a $b $(tail -2 $a.client.log | tr '\n' ' ' | cut -c1-300)" >> chain2.log
  if grep -q '"exit_status": 124' $a.client.log; then echo "timeout $b" >> chain2.log; fi
  i=$((i+1))
done
echo done >> chain2.log
