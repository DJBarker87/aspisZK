"""Job admission: require quiet-window clearance, allowed:true, and exit zero."""
from pathlib import Path
import json,subprocess,sys,time
out=Path(sys.argv[1]);quiet=Path('/home/dombarker/project-offloads/QUIET_WINDOW.json')
if quiet.exists() and time.time()<json.loads(quiet.read_text())['until']:
 out.write_text(json.dumps(dict(allowed=False,reason='QUIET WINDOW HOLD',window=json.loads(quiet.read_text())))+'\n');sys.exit(78)
r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py',str(out)],capture_output=True,text=True)
print(r.stdout,end='');print(r.stderr,end='',file=sys.stderr)
if r.returncode!=0 or not out.exists() or json.loads(out.read_text()).get('allowed') is not True:sys.exit(78 if r.returncode in (0,78) else r.returncode)
