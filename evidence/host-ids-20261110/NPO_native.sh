#!/bin/bash
# NPO_ native tool build/run inside a capped scope. Usage:
#   NPO_native.sh build <label> <Src>      (lean -c then leanc -O3 link; Src imports only Lean core)
#   NPO_native.sh run <label> <Exe> <args...>   (180 s, LEAN_PATH = own out + L187 objs + base_ref)
set -u
[ "$(pgrep -c -x lean)" -lt 6 ] || { echo "HOST LEAN COUNT >= 6"; exit 4; }
W=/home/dombarker/project-offloads/codex-cx-hostids-20261110
R=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109
T=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
mode=$1; L=$2; shift 2; D=$W/logs/$L; mkdir -p $D $W/native
python3 - "$D" <<'PY' || { echo "RESERVATION REFUSED"; exit 3; }
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
RUN="systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 env -i PATH=/usr/bin:/bin LEAN_SYSROOT=$T LEAN_PATH=$W/out:$R/objs:$R/base_ref TMPDIR=$W/tmp"
if [ $mode = build ]; then
  S=$1; sha=$(sha256sum src/$S.lean | cut -d' ' -f1)
  $RUN /usr/bin/time -v -o $D/time.log timeout 180 sh -c "$T/bin/lean -j1 -M7000 -DElab.async=false -c native/$S.c src/$S.lean && $T/bin/leanc -O3 -rdynamic -o native/$S native/$S.c" > $D/stdout.log 2>&1
else
  X=$1; shift; sha=$(sha256sum native/$X | cut -d' ' -f1)
  ( cd $W/logs/$L && $RUN /usr/bin/time -v -o $D/time.log timeout 180 $W/native/$X "$@" ) > $D/stdout.log 2>&1
fi
ec=$?
rss=$(grep 'Maximum resident' $D/time.log | awk '{print $NF}')
wall=$(grep 'Elapsed (wall' $D/time.log | awk '{print $NF}')
swap=$(grep 'Swaps' $D/time.log | awk '{print $NF}')
printf '{"label":"%s","mode":"%s","target_sha256":"%s","args":"%s","exit":%s,"wall":"%s","peak_rss_kib":"%s","swaps":"%s","caps":"MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64; timeout 180","lean":"v4.32.0","lean_path":"out:L187 objs:L187 base_ref"}\n' \
  "$L" "$mode" "$sha" "$*" "$ec" "$wall" "$rss" "$swap" > $D/receipt.json
cat $D/receipt.json; tail -30 $D/stdout.log
