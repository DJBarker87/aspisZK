#!/bin/sh
# c3/send.sh <attempt 4340-4399> <Module e.g. R1Z/CertCheckExtracted> : copy one module to the build host and
# compile it with run2-par.sh (in-window) / global lock (outside).  Refuses an already-sent sha256 (rule 9)
# and waits while another Lean/Aeneas/Charon/cargo job runs on the host (rule 5 gate).
set -u
A=$1; M=$2; H=dombarker@100.108.41.90; T=/home/dombarker/project-offloads/aspis-fs-generic-20261006
D=$(cd "$(dirname "$0")" && pwd); L=$D/../lean/$M.lean; LED=$D/evidence/lean-sent.txt
{ [ "$A" -ge 4340 ] && [ "$A" -le 4399 ]; } || { [ "$A" -ge 4460 ] && [ "$A" -le 4519 ]; } || { echo "attempt out of range"; exit 2; }
SHA=$(shasum -a 256 "$L" | cut -d' ' -f1)
touch "$LED"
# DEPREPLAY=1: the source is unchanged but a dependency object was rebuilt (lead-authorised dependency replay).
if [ "${DEPREPLAY:-0}" != 1 ] && grep -q "$SHA" "$LED"; then echo "REFUSE: sha $SHA already sent: $(grep $SHA $LED)"; exit 3; fi
if grep -q "^$A " "$LED"; then echo "REFUSE: attempt $A already used"; exit 3; fi
while ssh $H "ps -eo cmd | grep -E '(^| |/)(lean|aeneas|charon|cargo|rustc)( |$)|lake ' | grep -v grep | grep -q ."; do sleep 5; done
ssh $H "mkdir -p $T/sources/$(dirname $M)" && scp -q "$L" $H:$T/sources/$M.lean || exit 4
echo "$A $M $SHA $(date -u +%FT%TZ)$([ "${DEPREPLAY:-0}" = 1 ] && echo " dependency-replay")" >> "$LED"
ssh $H "RUN2_GLOBAL=${RUN2_GLOBAL:-0} sh $T/run2-par.sh $A $M 7000 7"
