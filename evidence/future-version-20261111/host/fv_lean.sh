#!/bin/bash
# Aspis per-step accounting: ONE capped Lean compile at a time, shared by several agents.
# Usage: fv_lean.sh <attempt> <Module>
#   source  $W/lean-src/<Module>.lean        object  $W/lean-out/<Module>.olean
#   receipt $W/receipts/<attempt>/{exit,stdout.log,stderr.log,time.log,cgroup_memory_peak,...}
# A lock serializes our own compiles (the soundness lead's recipe says one at a time). Admission is
# the rule of fv_scope.sh (fewer than 5 other running scopes, their MemoryMax plus 8 GiB at most
# 55 GiB), retried every 20 s for up to 15 minutes, because these compiles take seconds.
# Scope: MemoryHigh 6G, MemoryMax 8G, no swap, TasksMax 64. Lean 4.32.0 against the L187 release
# objects by reference (never written).
set -u
W=/home/dombarker/project-offloads/future-version-20261111
A=$1; M=$2
R=$W/receipts/$A
test ! -e $R || { echo "receipt exists: $R (use a new attempt name)"; exit 2; }
test -f $W/lean-src/$M.lean || { echo "no source: $W/lean-src/$M.lean"; exit 2; }
mkdir -p $R
exec 9> $W/lean.lock
flock 9
G=$((1024*1024*1024))
for i in $(seq 0 45); do
  n=0; sum=0
  for s in $(systemctl --user list-units --type=scope --state=running --no-legend | awk '$1!="init.scope"{print $1}'); do
    m=$(systemctl --user show -p MemoryMax --value $s); n=$((n+1))
    case $m in infinity|"") sum=$((sum+64*G));; *) sum=$((sum+m));; esac
  done
  echo "$(date -u +%FT%TZ) try=$i other_scopes=$n other_memory_max_bytes=$sum" >> $R/admission.log
  if [ $n -lt 5 ] && [ $((sum+8*G)) -le $((55*G)) ]; then break; fi
  if [ $i -eq 45 ]; then echo REFUSED >> $R/admission.log; echo "$A not admitted in 15 minutes"; exit 75; fi
  sleep 20
done
echo "$M" > $R/argv.txt
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  bash -c 'cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup); for f in memory.high memory.max memory.swap.max pids.max; do echo "$f $(cat $cg/$f)"; done > '"$R"'/limits.txt; /usr/bin/time -v -o '"$R"'/time.log bash '"$W"'/fv_lean_one.sh '"$M"' > '"$R"'/stdout.log 2> '"$R"'/stderr.log; rc=$?; echo $rc > '"$R"'/exit; cat $cg/memory.peak > '"$R"'/cgroup_memory_peak 2>/dev/null; cat $cg/memory.events > '"$R"'/memory_events 2>/dev/null; exit $rc'
rc=$?
echo "$A $M exit $rc; wall $(grep -o "Elapsed.*" $R/time.log | awk "{print \$NF}"); rss_kb $(grep "Maximum resident" $R/time.log | awk "{print \$NF}")"
head -c 1500 $R/stdout.log
head -c 1500 $R/stderr.log
exit $rc
