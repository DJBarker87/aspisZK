"""Honor the first refused launch's cooldown, then use fresh native receipt labels."""
from pathlib import Path
import datetime,json,subprocess,sys,time
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
run_id=int(sys.argv[1]);prior=sys.argv[2]
p=H/'candidate'/prior/'reservation.json';j=json.loads(p.read_text());assert j['allowed'] is False
stamp=j.get('utc',p.stat().st_mtime)
if isinstance(stamp,str):stamp=datetime.datetime.fromisoformat(stamp).timestamp()
while time.time()<stamp+180:time.sleep(min(60,stamp+180-time.time()))
raise SystemExit(subprocess.run(['python3',str(H/'retry-native.py'),f'batch2b-extract{run_id}-retry','1','python3',str(H/'extract-batch2b.py'),str(run_id)]).returncode)
