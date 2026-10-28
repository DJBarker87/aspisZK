#!/usr/bin/env bash
set -euo pipefail
D=/home/dombarker/project-offloads/codex-pv-gate6-20261028
M=/home/dombarker/project-offloads/QUIET_WINDOW.json
cd "$D"
cleanup() {
  if [[ -f "$D/measurement-scope/launch-intent.json" ]]; then
    systemctl --user stop pv-gate6-measurement.scope > "$D/measurement-scope/cleanup-stop.log" 2>&1 || true
  fi
  python3 - "$D" "$M" <<'PY'
from pathlib import Path
import sys,json,time
D=Path(sys.argv[1]);m=Path(sys.argv[2]);r=dict(cleanup_time=time.time(),removed=False)
if (D/'window-start.json').exists():
 own=json.loads((D/'window-start.json').read_text())
 if m.exists() and json.loads(m.read_text())==own:
  m.unlink();r.update(removed=True,marker_removal_time=time.time())
(D/'window-cleanup.json').write_text(json.dumps(r,indent=2)+'\n')
PY
}
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
# Establish the marker before any drain check. Never replace another marker.
python3 - "$D" "$M" <<'PY'
from pathlib import Path
import sys,json,time,os
D=Path(sys.argv[1]);m=Path(sys.argv[2]);start=time.time()
r=dict(until=start+1500,owner='stream-b-pv-gate6',purpose='candidate timing gate')
fd=os.open(m,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o644)
with os.fdopen(fd,'w') as f:json.dump(r,f);f.write('\n')
(D/'window-start.json').write_text(json.dumps(r,indent=2)+'\n')
(D/'window-clock.json').write_text(json.dumps(dict(start=start,until=r['until'],never_extended=True),indent=2)+'\n')
PY
python3 - "$D" <<'PY'
from pathlib import Path
import subprocess,time,json,sys
D=Path(sys.argv[1]);start=time.monotonic()
for i in range(61):
 p=D/f'drain-{i:02d}.json'
 r=subprocess.run(['python3',str(D/'quiet-preflight.py'),str(p)],stdout=subprocess.DEVNULL)
 (D/f'drain-{i:02d}.cgls.txt').write_text(subprocess.run(['systemd-cgls','--user','--no-pager'],capture_output=True,text=True).stdout)
 if r.returncode==0:
  (D/'drain-complete.json').write_text(json.dumps(dict(seconds=time.monotonic()-start,utc=time.time(),checks=i+1),indent=2)+'\n');break
 if r.returncode!=78:raise SystemExit(r.returncode)
 if time.monotonic()-start>=600:raise SystemExit('Drain exceeded ten minutes; no measurement')
 time.sleep(min(10,600-(time.monotonic()-start)))
else:raise SystemExit('Drain limit')
PY
export QUIET_WINDOW_OWNER=1
# Own measurement scope must end before the immutable expiry.
remaining=$(python3 -c 'import json,time; print(max(1,int(json.load(open("window-start.json"))["until"]-time.time()-2)))')
python3 - "$D" <<'PY'
from pathlib import Path
import subprocess,json,sys
D=Path(sys.argv[1]);o=D/'measurement-scope';o.mkdir()
r=subprocess.run(['python3',str(D/'reservation.py'),str(o/'admission.json')],stdout=open(o/'reservation.log','w'),stderr=subprocess.STDOUT)
assert r.returncode==0 and json.loads((o/'admission.json').read_text())['allowed'],'measurement admission refused'
PY
python3 - "$D" <<'PYINTENT'
from pathlib import Path
import sys,time,json
D=Path(sys.argv[1]);(D/'measurement-scope/launch-intent.json').write_text(json.dumps(dict(unit='pv-gate6-measurement.scope',utc=time.time()),indent=2)+'\n')
PYINTENT
systemd-run --user --scope --unit=pv-gate6-measurement -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  python3 /home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/barrier.py "$D/measurement-scope/barrier.json" \
  python3 "$D/capped.py" "$D/measurement-scope/receipt" 'optimized paired proof generation and P_R1 elimination; no compilation' -- \
  timeout --signal=TERM --kill-after=2 "$remaining" python3 "$D/measure.py" > "$D/measurement-scope/scope.log" 2>&1
# Remove as soon as measurement exits; EXIT trap also covers failures.
cleanup
trap - EXIT
