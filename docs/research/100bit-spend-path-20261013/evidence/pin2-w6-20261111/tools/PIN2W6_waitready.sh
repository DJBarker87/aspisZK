#!/bin/zsh
# Repeat: wait for an overlay-HOST-P1.sha256 refresh, rescan, plan; when at least one
# fixture-named or direct-consumer module is ready, run the cycle and exit.
# usage: PIN2W6_waitready.sh <batch> <max_wait_s>
T=$(cd $(dirname $0) && pwd); W6=$(dirname $T)
SP=/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad/w6
F=/Users/dominic/aspis-lead-infra/l187-closure/overlay-HOST-P1.sha256
end=$(( $(date +%s) + $2 ))
while [ $(date +%s) -lt $end ]; do
  m0=$(stat -f %m $F)
  until [ $(stat -f %m $F) != $m0 ] || [ $(date +%s) -ge $end ]; do sleep 20; done
  [ $(stat -f %m $F) = $m0 ] && break
  sleep 5
  $T/PIN2W6_rescan.sh $SP >/dev/null
  n=$(cd $T && python3 -I PIN2W6_ready.py $SP >/dev/null && python3 -I -c "
import json,re
r=json.load(open('$SP/plan.json'))['ready']
FIX=re.compile(r'^(NDO_J[A-Z]|RPt_J[A-Z]|RPu_J[A-Z]|RPz8_J[A-Z]|J[A-Z][a-z]_)')
D=set(open('$W6/DIRECT-CONSUMERS.txt').read().split())
print(sum(1 for m in r if FIX.match(m) or m in D))")
  echo "$(date -u +%H:%M) HOST-P1 $(wc -l < $F | tr -d ' '): ready fixture/direct $n"
  if [ "$n" -gt 0 ]; then $T/PIN2W6_cycle.sh $1 only-fixture; exit 0; fi
done
echo "no fixture module became ready"
