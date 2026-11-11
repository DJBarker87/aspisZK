#!/bin/bash
# Future-version experiment: one capped scope per call (adapted from PCXS_elf_scope.sh).
# Usage: fv_scope.sh <attempt> <timeout-seconds> <cmd...>
# Admission: fewer than 5 other running user scopes, their summed MemoryMax plus this
# scope's 8 GiB at most 55 GiB, and at least 45 GB free disk (waits 3 min, up to 6 times).
set -u
W=/home/dombarker/project-offloads/future-version-20261111
A=$1; TO=$2; shift 2
R=$W/receipts/$A
test ! -e $R || { echo "receipt exists: $R (unchanged rerun refused)"; exit 2; }
mkdir -p $R
G=$((1024*1024*1024))
for i in 0 1 2 3 4 5 6; do
  n=0; sum=0
  for s in $(systemctl --user list-units --type=scope --state=running --no-legend | awk '$1!="init.scope"{print $1}'); do
    m=$(systemctl --user show -p MemoryMax --value $s); n=$((n+1))
    case $m in infinity|"") sum=$((sum+64*G));; *) sum=$((sum+m));; esac
    echo "$s $m" >> $R/scopes_before.txt
  done
  d=$(df -BG --output=avail /home | tail -1 | tr -dc 0-9)
  echo "$(date -u +%FT%TZ) try=$i other_scopes=$n other_memory_max_bytes=$sum disk_free_G=$d" >> $R/admission.log
  if [ $n -lt 5 ] && [ $((sum+8*G)) -le $((55*G)) ] && [ $d -ge 45 ]; then break; fi
  if [ $i -eq 6 ]; then echo REFUSED >> $R/admission.log; exit 75; fi
  sleep 180
done
echo "$@" > $R/argv.txt
start=$(date +%s.%N)
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=256 \
  bash -c 'cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup); echo $cg > '"$R"'/cgroup.txt; for f in memory.high memory.max memory.swap.max pids.max; do echo "$f $(cat $cg/$f)"; done > '"$R"'/limits.txt; /usr/bin/time -v -o '"$R"'/time.log timeout '"$TO"' "$@" > '"$R"'/stdout.log 2> '"$R"'/stderr.log; rc=$?; echo $rc > '"$R"'/exit; cat $cg/memory.peak > '"$R"'/cgroup_memory_peak 2>/dev/null; cat $cg/memory.swap.peak > '"$R"'/cgroup_swap_peak 2>/dev/null; cat $cg/memory.events > '"$R"'/memory_events 2>/dev/null; exit $rc' _ "$@"
rc=$?
end=$(date +%s.%N)
echo "$start $end" > $R/scope_wall
echo "$A scope exit $rc"
exit $rc
