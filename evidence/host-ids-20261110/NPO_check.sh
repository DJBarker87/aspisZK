#!/bin/bash
# NPO_ independent kernel replay with the toolchain's leanchecker (Lean.Environment.replay of every
# constant of the target module into its import environment), inside an 8G capped scope.
# Usage: NPO_check.sh <label> <Module>
set -u
[ "$(pgrep -c -x lean)" -lt 6 ] || { echo "HOST LEAN COUNT >= 6"; exit 4; }
W=/home/dombarker/project-offloads/codex-cx-hostids-20261110
R=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109
T=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
L=$1; M=$2; D=$W/logs/$L; mkdir -p $D
python3 - "$D" <<'PY' || { echo "RESERVATION REFUSED"; exit 3; }
import json,sys,glob,shutil,time
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
json.dump({'utc':time.time(),'populated_capped_scopes':len(scopes),'sum_memory_max':tot,'requested':8*2**30,'disk_free':free,'allowed':ok,'scopes':scopes},open(d+'/reservation.json','w'),indent=1)
sys.exit(0 if ok else 1)
PY
olean_sha=$(sha256sum $W/out/$M.olean | cut -d' ' -f1); chk_sha=$(sha256sum $T/bin/leanchecker | cut -d' ' -f1)
CMD="$T/bin/leanchecker -v $M"
cd $D
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  env -i PATH=$T/bin:/usr/bin:/bin LEAN_SYSROOT=$T LEAN_PATH=$W/out:$R/objs:$R/base_ref TMPDIR=$W/tmp \
  /usr/bin/time -v -o $D/time.log timeout 180 $CMD > $D/stdout.log 2>&1
ec=$?
rss=$(grep 'Maximum resident' $D/time.log | awk '{print $NF}'); wall=$(grep 'Elapsed (wall' $D/time.log | awk '{print $NF}'); swap=$(grep 'Swaps' $D/time.log | awk '{print $NF}')
printf '{"label":"%s","command":"%s","cwd":"%s","module":"%s","olean_sha256":"%s","leanchecker_sha256":"%s","exit":%s,"wall":"%s","peak_rss_kib":"%s","swaps":"%s","caps":"MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64; timeout 180","env":"PATH=T/bin:/usr/bin:/bin LEAN_SYSROOT=T LEAN_PATH=out:L187 objs:L187 base_ref"}\n' \
  "$L" "$CMD" "$D" "$M" "$olean_sha" "$chk_sha" "$ec" "$wall" "$rss" "$swap" > $D/receipt.json
cat $D/receipt.json; tail -20 $D/stdout.log
