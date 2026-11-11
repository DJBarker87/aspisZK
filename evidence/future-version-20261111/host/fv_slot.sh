#!/bin/bash
# Aspis: ONE capped job in one of our three host slots (shared with fv_lean.sh: same slot locks,
# same block reservation, scopes named fvlean-*). For jobs that are not single Lean compiles:
# cargo builds, replays, the extraction probe.
# Usage: fv_slot.sh <attempt> <timeout-seconds> <cmd...>
#   receipt $W/receipts/<attempt>/{argv.txt,exit,stdout.log,stderr.log,time.log,cgroup_memory_peak,limits.txt}
# Scope: MemoryHigh 6G, MemoryMax 8G, no swap, TasksMax 256. Never raise the cap; a job killed for
# memory is restructured, not retried.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
A=$1; TO=$2; shift 2
R=$W/receipts/$A
test ! -e $R || { echo "receipt exists: $R (use a new attempt name)"; exit 2; }
mkdir -p $R
slot=""
while [ -z "$slot" ]; do
  for k in 1 2 3; do
    exec {fd}> $W/lean.lock.$k
    if flock -n $fd; then slot=$k; break; else exec {fd}>&-; fi
  done
  [ -n "$slot" ] || sleep 2
done
echo "slot $slot" > $R/slot.txt
# Each slot has its own four cores (slot 1: 0-3, slot 2: 4-7, slot 3: 8-11). The scripts name
# --cpu-list 0-3 everywhere; slotbin/taskset replaces that list by the slot's cores.
export FV_CPUS=$(( (slot-1)*4 ))-$(( (slot-1)*4+3 ))
export PATH=$W/slotbin:$PATH
echo "cpus $FV_CPUS" >> $R/slot.txt
G=$((1024*1024*1024))
for i in $(seq 0 45); do
  n=0; sum=0
  for s in $(systemctl --user list-units --type=scope --state=running --no-legend | awk '$1!="init.scope" && $1 !~ /^fvlean-/{print $1}'); do
    m=$(systemctl --user show -p MemoryMax --value $s); n=$((n+1))
    case $m in infinity|"") sum=$((sum+64*G));; *) sum=$((sum+m));; esac
  done
  echo "$(date -u +%FT%TZ) try=$i other_stream_scopes=$n other_stream_memory_max_bytes=$sum" >> $R/admission.log
  if [ $((sum+24*G)) -le $((55*G)) ]; then break; fi
  if [ $i -eq 45 ]; then echo REFUSED >> $R/admission.log; echo "$A not admitted in 15 minutes"; exit 75; fi
  sleep 20
done
printf '%s\n' "$@" > $R/argv.txt
start=$(date +%s.%N)
systemd-run --user --scope -q --unit=fvlean-$slot-$$ -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=256 \
  bash -c 'R='"$R"'; cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup); for f in memory.high memory.max memory.swap.max pids.max; do echo "$f $(cat $cg/$f)"; done > $R/limits.txt; /usr/bin/time -v -o $R/time.log timeout '"$TO"' "$@" > $R/stdout.log 2> $R/stderr.log; rc=$?; echo $rc > $R/exit; cat $cg/memory.peak > $R/cgroup_memory_peak 2>/dev/null; cat $cg/memory.events > $R/memory_events 2>/dev/null; exit $rc' fv_slot "$@"
rc=$?
echo "$start $(date +%s.%N)" > $R/scope_wall
echo "$A exit $rc; wall $(grep -o "Elapsed.*" $R/time.log | awk "{print \$NF}"); rss_kb $(grep "Maximum resident" $R/time.log | awk "{print \$NF}")"
exit $rc
