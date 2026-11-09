#!/bin/bash
# NOX_ capped scope launcher. Usage: NOX_scope.sh <attempt> <class:build|ordinary> <cmd...>
# Admission: other running user scopes < 5 and host free disk >= 40 GB (waits 10 min, up to 6 times).
set -u
W=/home/dombarker/project-offloads/codex-cx-l188-20261109
A=$1; CLASS=$2; shift 2
if [ "$CLASS" = build ]; then TO=1800; else TO=180; fi
R=$W/receipts/$A; mkdir -p $R
for i in 0 1 2 3 4 5 6; do
  n=$(systemctl --user list-units --type=scope --state=running --no-legend | grep -c '^ *run-')
  d=$(df -BG --output=avail /home | tail -1 | tr -dc 0-9)
  echo "$(date -u +%FT%TZ) admission try=$i other_scopes=$n disk_free_G=$d" >> $R/admission.log
  if [ "$n" -lt 5 ] && [ "$d" -ge 40 ]; then break; fi
  if [ $i -eq 6 ]; then echo REFUSED >> $R/admission.log; exit 75; fi
  sleep 600
done
systemctl --user list-units --type=scope --state=running --no-legend > $R/scopes_before.txt
for s in $(systemctl --user list-units --type=scope --state=running --no-legend | awk '/^ *run-/{print $1}'); do
  echo "$s $(systemctl --user show -p MemoryMax --value $s)" >> $R/scopes_before.txt; done
echo "$@" > $R/argv.txt
start=$(date +%s.%N)
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  bash -c 'cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup); echo $cg > '"$R"'/cgroup.txt; for f in memory.high memory.max memory.swap.max pids.max; do echo "$f $(cat $cg/$f)"; done > '"$R"'/limits.txt; env | sort > '"$R"'/env_outer.txt; /usr/bin/time -v -o '"$R"'/time.log timeout '"$TO"' "$@" > '"$R"'/stdout.log 2> '"$R"'/stderr.log; rc=$?; echo $rc > '"$R"'/exit; cat $cg/memory.peak > '"$R"'/cgroup_memory_peak 2>/dev/null; cat $cg/memory.swap.peak > '"$R"'/cgroup_swap_peak 2>/dev/null; cat $cg/memory.events > '"$R"'/memory_events 2>/dev/null; exit $rc' _ "$@"
rc=$?
end=$(date +%s.%N)
echo "$start $end" > $R/scope_wall
echo "scope exit $rc"
exit $rc
