#!/bin/bash
# NPP_ capped Lean scope launcher (build host). Usage: NPP_run_host.sh <label> <Module> [timeout_s]
# Gates (lead, 2026-11-10): host lean count < 6; at most 1 NPP scope at a time; `free -g` available >= 12;
#   sum(MemoryMax of populated capped scopes)+8G <= 55 GiB; >= 40 GB disk free.
# Scope: MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64; lean -j1 -M7000 -DElab.async=false;
#   timeout 180 s (600 s only for the one labelled timing probe).
# LEAN_PATH (by reference, read-only): own out/, NPO_ out/, the L187 replayed objs/ and base_ref/.
set -u
W=/home/dombarker/project-offloads/codex-cx-nonvac-20261110
N=/home/dombarker/project-offloads/codex-cx-hostids-20261110
R=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109
T=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
L=$1; M=$2; TO=${3:-180}; D=$W/logs/$L; mkdir -p $D
[ "$TO" -le 600 ] || { echo "TIMEOUT ABOVE 600 REFUSED"; exit 5; }
[ "$(pgrep -c -x lean)" -lt 6 ] || { echo "HOST LEAN COUNT >= 6"; exit 4; }
pgrep -f "$W/(src|native)/|leanchecker -v NPP_"  >/dev/null && { echo "ANOTHER NPP SCOPE RUNNING"; exit 6; }
avail=$(free -g | awk '/^Mem:/{print $7}')
[ "$avail" -ge 12 ] || { echo "AVAILABLE MEMORY ${avail}G < 12G"; exit 7; }
python3 - "$D" "$avail" <<'PY' || { echo "RESERVATION REFUSED"; cat "$1/reservation.json" 2>/dev/null; exit 3; }
import json,os,sys,glob,shutil,time
d=sys.argv[1]; base='/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice'
scopes=[]
for s in glob.glob(base+'/*.scope'):
    try:
        if not open(s+'/cgroup.procs').read().strip(): continue
        mm=open(s+'/memory.max').read().strip()
        if mm=='max': continue
        scopes.append({'scope':s,'memory_max':int(mm)})
    except Exception: pass
tot=sum(x['memory_max'] for x in scopes); free=shutil.disk_usage('/home').free
ok=tot+8*2**30<=55*2**30 and free>=40*10**9  # 2026-11-10: scope-count heuristic dropped (owner slot allocation: Stream C 5, Stream A 1); memory sum, disk, lean count, free memory, one NPP scope kept
json.dump({'utc':time.time(),'free_g_available':int(sys.argv[2]),'populated_capped_scopes':len(scopes),'sum_memory_max':tot,
  'requested':8*2**30,'disk_free':free,'allowed':ok,'scopes':scopes},open(d+'/reservation.json','w'),indent=1)
sys.exit(0 if ok else 1)
PY
cd $W
src=$(sha256sum src/$M.lean | cut -d' ' -f1)
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  env -i PATH=/usr/bin:/bin LEAN_SYSROOT=$T LEAN_PATH=$W/out:$N/out:$R/objs:$R/base_ref TMPDIR=$W/tmp \
  /usr/bin/time -v -o $D/time.log timeout $TO $T/bin/lean -j1 -M7000 -DElab.async=false \
  -o $W/out/$M.olean $W/src/$M.lean > $D/stdout.log 2>&1
ec=$?
rss=$(grep 'Maximum resident' $D/time.log | awk '{print $NF}')
wall=$(grep 'Elapsed (wall' $D/time.log | awk '{print $NF}')
swap=$(grep 'Swaps' $D/time.log | awk '{print $NF}')
printf '{"label":"%s","module":"%s","source_sha256":"%s","exit":%s,"wall":"%s","peak_rss_kib":"%s","swaps":"%s","caps":"MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64; lean -j1 -M7000 -DElab.async=false; timeout %s","lean":"v4.32.0","lean_path":"own out:NPO out:L187 objs:L187 base_ref"}\n' \
  "$L" "$M" "$src" "$ec" "$wall" "$rss" "$swap" "$TO" > $D/receipt.json
cat $D/receipt.json; tail -c 6000 $D/stdout.log
