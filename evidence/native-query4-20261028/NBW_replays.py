from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for row in json.loads((E/'NBW_REPLAY_PLAN.json').read_text()):
 r=subprocess.run([sys.executable,str(E/'NBW_run.py'),row['attempt'],row['harness']])
 if r.returncode:raise SystemExit(r.returncode)
