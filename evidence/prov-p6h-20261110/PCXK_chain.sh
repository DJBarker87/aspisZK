#!/bin/bash
# serial chain over plan scopes N..M (descending est. wall order reversed: light first); stops when a step exits with something other than 0/1 (timeout/kill) or the client fails
cd "$(dirname "$0")"
for n in $(seq "$1" -1 "$2"); do
  bash PCXK_go.sh $n
  A=$(python3 -c "import json,sys;print(json.load(open('PCXK_PLAN.json'))['scopes'][int(sys.argv[1])-1]['attempt'])" $n)
  if [ ! -f $A/receipt.json ]; then echo "STOP no receipt $A" >> PCXK_chain.log; exit 3; fi
  bad=$(python3 -c "import json,sys;r=json.load(open(sys.argv[1]));print(sum(1 for s in r['steps'] if s['exit_status'] not in (0,1)))" $A/receipt.json)
  echo "$A done bad=$bad" >> PCXK_chain.log
  if [ "$bad" != "0" ]; then echo "STOP infra exit in $A" >> PCXK_chain.log; exit 4; fi
done
echo CHAIN_DONE >> PCXK_chain.log
