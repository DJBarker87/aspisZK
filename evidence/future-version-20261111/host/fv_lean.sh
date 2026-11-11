#!/bin/bash
# Aspis per-step accounting: capped Lean compiles shared by several agents, at most three at a time.
# Usage: fv_lean.sh <attempt> <Module>
#   source  $W/lean-src/<Module>.lean        object  $W/lean-out/<Module>.olean
#   receipt $W/receipts/<attempt>/{exit,stdout.log,stderr.log,time.log,cgroup_memory_peak,...}
# Three slot locks bound our own concurrency. Admission is by the host reservation: the MemoryMax
# of the other streams' running scopes plus our three slots (24 GiB) must be at most 55 GiB,
# retried every 20 s for up to 15 minutes.
# Scope: MemoryHigh 6G, MemoryMax 8G, no swap, TasksMax 64. Lean 4.32.0 against the L187 release
# objects by reference (never written).
set -u
W=/home/dombarker/project-offloads/future-version-20261111
A=$1; M=$2
R=$W/receipts/$A
test ! -e $R || { echo "receipt exists: $R (use a new attempt name)"; exit 2; }
test -f $W/lean-src/$M.lean || { echo "no source: $W/lean-src/$M.lean"; exit 2; }
mkdir -p $R
# Up to THREE of our compiles at a time (owner, 2026-11-11: "use up to 3 slots"): take one of three slot locks.
slot=""
while [ -z "$slot" ]; do
  for k in 1 2 3; do
    exec {fd}> $W/lean.lock.$k
    if flock -n $fd; then slot=$k; break; else exec {fd}>&-; fi
  done
  [ -n "$slot" ] || sleep 2
done
echo "slot $slot" > $R/slot.txt
G=$((1024*1024*1024))
for i in $(seq 0 45); do
  n=0; sum=0
  # Scopes of other streams only (ours are named fvlean-*). Our three slots are reserved as a
  # block, so that simultaneous admissions cannot overshoot: others + 3 x 8 GiB <= 55 GiB.
  for s in $(systemctl --user list-units --type=scope --state=running --no-legend | awk '$1!="init.scope" && $1 !~ /^fvlean-/{print $1}'); do
    m=$(systemctl --user show -p MemoryMax --value $s); n=$((n+1))
    case $m in infinity|"") sum=$((sum+64*G));; *) sum=$((sum+m));; esac
  done
  echo "$(date -u +%FT%TZ) try=$i other_stream_scopes=$n other_stream_memory_max_bytes=$sum" >> $R/admission.log
  if [ $((sum+24*G)) -le $((55*G)) ]; then break; fi
  if [ $i -eq 45 ]; then echo REFUSED >> $R/admission.log; echo "$A not admitted in 15 minutes"; exit 75; fi
  sleep 20
done
echo "$M" > $R/argv.txt
systemd-run --user --scope -q --unit=fvlean-$slot-$$ -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  bash -c 'cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup); for f in memory.high memory.max memory.swap.max pids.max; do echo "$f $(cat $cg/$f)"; done > '"$R"'/limits.txt; /usr/bin/time -v -o '"$R"'/time.log bash '"$W"'/fv_lean_one.sh '"$M"' > '"$R"'/stdout.log 2> '"$R"'/stderr.log; rc=$?; echo $rc > '"$R"'/exit; cat $cg/memory.peak > '"$R"'/cgroup_memory_peak 2>/dev/null; cat $cg/memory.events > '"$R"'/memory_events 2>/dev/null; exit $rc'
rc=$?
echo "$A $M exit $rc; wall $(grep -o "Elapsed.*" $R/time.log | awk "{print \$NF}"); rss_kb $(grep "Maximum resident" $R/time.log | awk "{print \$NF}")"
head -c 1500 $R/stdout.log
head -c 1500 $R/stderr.log
exit $rc
