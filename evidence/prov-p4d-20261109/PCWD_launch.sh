#!/bin/bash
# usage: bash PCWD_launch.sh PCWD_L001 PCWD_ReachMeta.lean
set -u
A=$1; SRC=$2
E=$(cd "$(dirname "$0")" && pwd)
H=dombarker@100.108.41.90
W=/home/dombarker/project-offloads/codex-pc-prov-p4d-20261109
T=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
SSH="ssh -o ConnectTimeout=20 -o ServerAliveInterval=15 $H"
$SSH "timeout 60 mkdir -p $W/PCWD_sources $W/PCWD_tmp && cd $W && for f in S2W_run_host.py lakefile.toml lake-manifest.json lean-toolchain; do [ -e \$f ] || cp /home/dombarker/project-offloads/codex-cx-sound-int2-20261025/\$f . 2>/dev/null; done; ls" > $E/${A}-ws.log 2>&1
# (1) host scope count
$SSH "timeout 60 python3 -" > $E/${A}-hostscopes.json <<'PY'
import subprocess,pathlib,json
units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--no-pager'],text=True).splitlines();found=[]
for line in units:
 unit=line.split()[0];cg=subprocess.check_output(['systemctl','--user','show',unit,'-p','ControlGroup','--value'],text=True).strip();p=pathlib.Path('/sys/fs/cgroup'+cg)
 try:pids=(p/'cgroup.procs').read_text().split()
 except FileNotFoundError:continue
 for pid in pids:
  try:cwd=str(pathlib.Path('/proc/'+pid+'/cwd').resolve(strict=True))
  except Exception:continue
  if cwd.startswith('/home/dombarker/project-offloads/codex-'):found.append(unit);break
print(json.dumps(dict(scopes=found,count=len(found))))
PY
cat $E/${A}-hostscopes.json
python3 - "$E/${A}-hostscopes.json" <<'PY'
import json,sys
x=json.load(open(sys.argv[1])); sys.exit(0 if x['count']<6 else 3)
PY
[ $? -eq 0 ] || { echo "host scope count >= 6; wait"; exit 3; }
# (3) disk
$SSH "timeout 30 df -B1 --output=avail /home/dombarker/project-offloads | tail -1" > $E/${A}-disk.txt
python3 -c "import sys;sys.exit(0 if int(open('$E/${A}-disk.txt').read())>=40e9 else 4)" || { echo "disk <40GB"; exit 4; }
# (4) admission
$SSH "cd $W && timeout 60 python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py $W/${A}-reservation.json" > $E/${A}-barrier.log 2>&1
RC=$?
$SSH "cat $W/${A}-reservation.json" > $E/${A}-reservation.json
python3 - "$E/${A}-reservation.json" $RC <<'PY' || { echo "admission refused"; exit 5; }
import json,sys
d=json.load(open(sys.argv[1])); sys.exit(0 if (sys.argv[2]=='0' and d.get('allowed') is True) else 5)
PY
scp -o ConnectTimeout=20 $E/$SRC $H:$W/PCWD_sources/$SRC
REV=$(git -C $E rev-parse HEAD)
LP=$(python3 -c "import json;print(':'.join(json.load(open('$E/../ledger30-20261111/NNN_PATHS.json'))))")
python3 - "$E/${A}.json" "$A" "$SRC" "$T" "$LP" "$REV" "$W" <<'PY'
import json,sys
f,a,src,T,lp,rev,W=sys.argv[1:]
cfg=dict(attempt=a,kind='lean',module=src,sources=['PCWD_sources/'+src],
 command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','PCWD_sources','PCWD_sources/'+src],
 env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=W+'/PCWD_tmp',LEAN_PATH=lp),
 timeout=180,source_revision=rev,source_tree_dirty=False,deps_fingerprint={},expected_time='import elaboration (~25 s) plus bounded constant-graph walk')
json.dump(cfg,open(f,'w'))
PY
scp -o ConnectTimeout=20 $E/${A}.json $H:$W/${A}.json
$SSH "cd $W && timeout 300 systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py ${A}.json" > $E/${A}-launcher.log 2>&1
echo launcher exit $?
mkdir -p $E/$A
for f in receipt.json stdout.log time.log; do scp -o ConnectTimeout=20 $H:$W/$A/$f $E/$A/$f; done
tail -c 600 $E/${A}-launcher.log | head -c 600
