#!/bin/zsh
# One W6 cycle: rescan W4/HOST-P1 imports, plan ready fixture-downstream modules
# (in-closure only: the dep set is the release closure; with only-fixture, the
# fixture-named modules and the direct non-fixture consumers in DIRECT-CONSUMERS.txt),
# compile them in order,
# coherence check.  usage: PIN2W6_cycle.sh <batch-name> [only-fixture]
set -u
B=$1; ONLY=${2:-}
T=$(cd $(dirname $0) && pwd); W6=$(dirname $T)
SP=/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad/w6
$T/PIN2W6_rescan.sh $SP
cd $T && python3 -I PIN2W6_ready.py $SP | head -2
python3 -I -c "
import json,re
r=json.load(open('$SP/plan.json'))['ready']
FIX=re.compile(r'^(NDO_J[A-Z]|RPt_J[A-Z]|RPu_J[A-Z]|RPz8_J[A-Z]|J[A-Z][a-z]_)')
D=set(open('$W6/DIRECT-CONSUMERS.txt').read().split())
if '$ONLY': r=[m for m in r if FIX.match(m) or m in D]
open('$W6/BATCH-$B.txt','w').write('\n'.join(r)+('\n' if r else ''))
print('batch', len(r))"
[ -s $W6/BATCH-$B.txt ] && python3 -I PIN2W6_drive.py $SP $W6/BATCH-$B.txt "W6 batch $B" 2>&1 | tail -40
$T/PIN2W6_rescan.sh $SP >/dev/null
python3 -I PIN2W6_coherence.py $SP $W6/COHERENCE-$B.json --w4 | head -4
