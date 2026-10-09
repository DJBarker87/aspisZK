#!/bin/sh
# run2.sh <attempt> <Module> [M-limit-MB] [MemoryMax G]  -- R0FS runs, objects2 mirror
set -u
T=/home/dombarker/project-offloads/aspis-fs-generic-20261006
A=$1; M=$2; ML=${3:-7000}; MX=${4:-9}
# reservation check: populated finite caps + this scope must stay below 55 GiB
tot=0; for d in /sys/fs/cgroup/*.slice /sys/fs/cgroup/*/*.slice /sys/fs/cgroup/*/*/*.scope /sys/fs/cgroup/*/*.scope; do [ -f $d/memory.max ] || continue; v=$(cat $d/memory.max); [ "$v" = max ] && continue; p=$(cat $d/cgroup.procs 2>/dev/null | wc -l); [ "$p" -gt 0 ] && tot=$((tot+v)); done
if [ $((tot/1073741824 + MX)) -gt 55 ]; then echo "RESERVATION HOLD: populated $((tot/1073741824)) GiB + $MX GiB > 55"; exit 78; fi
echo "reservation: populated $((tot/1073741824)) GiB + $MX GiB"
mkdir -p "$T/objects2/$(dirname $M)"
sha256sum "$T/sources/$M.lean" > "$T/evidence/sha-$A.txt"
systemd-run --user --scope --quiet -p MemoryHigh=$((MX-2))G -p MemoryMax=${MX}G -p MemorySwapMax=0 -p TasksMax=128 \
  /usr/bin/time -v -o "$T/evidence/time-$A.log" timeout 900 python3 "$T/evidence/run_g15_lake.py" "$T/evidence/environment-base.json" "$T/objects2" "$T/sources" "$T/objects2/$M.olean" "$T/sources/$M.lean" "$ML" > "$T/evidence/out-$A.log" 2>&1
echo "exit=$?" >> "$T/evidence/out-$A.log"
tail -n 60 "$T/evidence/out-$A.log"
grep -E "Elapsed|Maximum resident|Swaps|Exit status" "$T/evidence/time-$A.log"
