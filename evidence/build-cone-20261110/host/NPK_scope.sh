#!/bin/bash
# NPK_ capped scope launcher (NOX_scope.sh shape + the host 55 GiB reservation scan).
# Usage: NPK_scope.sh <attempt> <class:build|ordinary> <cmd...>
set -u
W=/home/dombarker/project-offloads/codex-cx-cone-20261110
RES=/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py
A=$1; CLASS=$2; shift 2
if [ "$CLASS" = build ]; then TO=1800; else TO=600; fi
R=$W/receipts/$A; mkdir -p $R
for i in 0 1 2 3 4 5 6; do
  n=$(systemctl --user list-units --type=scope --state=running --no-legend | grep -vc '^ *init.scope')
  d=$(df -BG --output=avail /home | tail -1 | tr -dc 0-9)
  python3 $RES $R/reservation.json > $R/reservation.log 2>&1
  ok=$(python3 -c "import json;print(json.load(open('$R/reservation.json')).get('allowed'))" 2>/dev/null)
  echo "$(date -u +%FT%TZ) admission try=$i other_scopes=$n disk_free_G=$d reservation_allowed=$ok" >> $R/admission.log
  if [ "$n" -lt 6 ] && [ "$d" -ge 40 ] && [ "$ok" = True ]; then break; fi
  if [ $i -eq 6 ]; then echo REFUSED >> $R/admission.log; exit 75; fi
  sleep 300
done
systemctl --user list-units --type=scope --state=running --no-legend > $R/scopes_before.txt
echo "$@" > $R/argv.txt
start=$(date +%s.%N)
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  bash -c 'cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup); echo $cg > '"$R"'/cgroup.txt; for f in memory.high memory.max memory.swap.max pids.max; do echo "$f $(cat $cg/$f)"; done > '"$R"'/limits.txt; /usr/bin/time -v -o '"$R"'/time.log timeout '"$TO"' "$@" > '"$R"'/stdout.log 2> '"$R"'/stderr.log; rc=$?; echo $rc > '"$R"'/exit; cat $cg/memory.peak > '"$R"'/cgroup_memory_peak 2>/dev/null; cat $cg/memory.swap.peak > '"$R"'/cgroup_swap_peak 2>/dev/null; cat $cg/memory.events > '"$R"'/memory_events 2>/dev/null; exit $rc' _ "$@"
rc=$?
end=$(date +%s.%N)
echo "$start $end" > $R/scope_wall
echo "scope exit $rc"
exit $rc
