#!/bin/bash
set -euo pipefail
H=/home/dombarker/project-offloads/codex-pv-quiet-20261027
M=/home/dombarker/project-offloads/QUIET_WINDOW.json
cleanup() {
 status=$?
 trap - EXIT HUP INT TERM
 python3 - "$M" "$H/window-end.json" "$status" <<'PY'
import json,sys,time,os
p=sys.argv[1]; now=time.time()
try:
 data=json.load(open(p))
 if data.get('owner')=='stream-b-pv-quiet':os.unlink(p); removed=time.time()
 else:raise RuntimeError('marker owner changed; retained')
except FileNotFoundError:removed=None
json.dump(dict(process_exit=int(sys.argv[3]),measurement_process_end=now,marker_removed=removed,marker_exists=os.path.exists(p)),open(sys.argv[2],'w'),indent=2)
PY
 exit "$status"
}
# A pre-marker strict guard follows the recorded <=15 minute quiet wait.
python3 "$H/quiet-preflight.py" "$H/quiet-final-before-marker.json" >/dev/null
python3 - "$M" "$H/window-start.json" <<'PY'
import json,sys,time
now=time.time(); marker=dict(until=now+3600,owner='stream-b-pv-quiet',purpose='op223 timing gate')
with open(sys.argv[1],'x') as f:json.dump(marker,f)
json.dump(dict(start=now,marker=marker),open(sys.argv[2],'w'),indent=2)
PY
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
export QUIET_WINDOW_OWNER=1
python3 - <<'PY'
from run import run,H
raise SystemExit(run('measurement-scope','candidate',['python3',str(H/'measure.py'),'measurement'],owner=True))
PY
