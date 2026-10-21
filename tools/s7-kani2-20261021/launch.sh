#!/bin/sh
set -eu
cd /home/dombarker/project-offloads/codex-cx-s7-kani2-20261021
export PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin
attempt=$1
shift
mkdir -p reservations
python3 - "$attempt" <<'PY'
import subprocess,json,sys,time
units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--plain'],text=True)
scopes=[];total=0
for line in units.splitlines():
 unit=line.split()[0]
 if unit=='init.scope':continue
 fields=dict(l.split('=',1) for l in subprocess.check_output(['systemctl','--user','show',unit,'-p','MemoryMax','-p','MemoryCurrent','-p','MemoryHigh','-p','MemorySwapMax'],text=True).splitlines())
 scopes.append(dict(unit=unit,**fields))
 if fields['MemoryMax'].isdigit():total+=int(fields['MemoryMax'])
 else:raise SystemExit('Uncapped non-init scope: '+unit)
assert total+8*2**30<55*2**30,(total,scopes)
open('reservations/'+sys.argv[1]+'.json','w').write(json.dumps(dict(time_unix=time.time(),active=scopes,reserved_bytes=total,requested_bytes=8*2**30,safe_limit_bytes=55*2**30),indent=2)+'\n')
PY
exec systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 tools/s7-kani2-20261021/host-run.py "$attempt" timeout --kill-after=10s 240s cargo kani --manifest-path tools/s7-kani2-20261021/Cargo.toml -j 4 --output-format terse --no-assertion-reach-checks --solver kissat -Z function-contracts -Z stubbing -Z unstable-options "$@" --cbmc-args --unwinding-assertions
