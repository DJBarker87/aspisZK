#!/bin/zsh
# Wait until overlay-HOST-P1.sha256 changes (lead pull loop), then run one cycle.
# usage: PIN2W6_waitcycle.sh <batch> [max_wait_s]
F=/Users/dominic/aspis-lead-infra/l187-closure/overlay-HOST-P1.sha256
m0=$(stat -f %m $F); end=$(( $(date +%s) + ${2:-1500} ))
until [ $(stat -f %m $F) != $m0 ] || [ $(date +%s) -ge $end ]; do sleep 15; done
[ $(stat -f %m $F) = $m0 ] && { echo "no HOST-P1 refresh"; exit 0; }
sleep 5; echo "HOST-P1 refreshed: $(wc -l < $F) objects"
$(dirname $0)/PIN2W6_cycle.sh $1 only-fixture
