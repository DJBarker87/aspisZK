#!/bin/bash
# NPO_ capped Lean scope launcher (build host). Usage: NPO_run_host.sh <label> <Module>
# Gate: < 6 populated capped scopes, sum(MemoryMax)+8G <= 55 GiB, >= 40 GB free.
# Scope: MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64; lean -j1 -M7000, 180 s.
# LEAN_PATH: own out/, then the L187 replayed objects and base_ref by reference (read-only).
set -u
[ "$(pgrep -c -x lean)" -lt 6 ] || { echo "HOST LEAN COUNT >= 6"; exit 4; }
W=/home/dombarker/project-offloads/codex-cx-hostids-20261110
R=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109
T=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
L=$1; M=$2; D=$W/logs/$L; mkdir -p $D
python3 - "$D" <<'PY' || { echo "RESERVATION REFUSED"; cat "$1/reservation.json" 2>/dev/null; exit 3; }
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
ok=len(scopes)<6 and tot+8*2**30<=55*2**30 and free>=40*10**9
json.dump({'utc':time.time(),'populated_capped_scopes':len(scopes),'sum_memory_max':tot,
  'requested':8*2**30,'disk_free':free,'allowed':ok,'scopes':scopes},open(d+'/reservation.json','w'),indent=1)
sys.exit(0 if ok else 1)
PY
cd $W
git_src=$(sha256sum src/$M.lean | cut -d' ' -f1)
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  env -i PATH=/usr/bin:/bin LEAN_SYSROOT=$T LEAN_PATH=$W/out:$R/objs:$R/base_ref TMPDIR=$W/tmp \
  /usr/bin/time -v -o $D/time.log timeout 180 $T/bin/lean -j1 -M7000 -DElab.async=false \
  -o $W/out/$M.olean src/$M.lean > $D/stdout.log 2>&1
ec=$?
rss=$(grep 'Maximum resident' $D/time.log | awk '{print $NF}')
wall=$(grep 'Elapsed (wall' $D/time.log | awk '{print $NF}')
swap=$(grep 'Swaps' $D/time.log | awk '{print $NF}')
printf '{"label":"%s","module":"%s","source_sha256":"%s","exit":%s,"wall":"%s","peak_rss_kib":"%s","swaps":"%s","caps":"MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64; lean -j1 -M7000 -DElab.async=false; timeout 180","lean":"v4.32.0","lean_path":"out:L187 objs:L187 base_ref"}\n' \
  "$L" "$M" "$git_src" "$ec" "$wall" "$rss" "$swap" > $D/receipt.json
cat $D/receipt.json; tail -40 $D/stdout.log
