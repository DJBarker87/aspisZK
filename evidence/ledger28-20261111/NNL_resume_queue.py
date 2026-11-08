from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
s=json.loads((E/'NNL_SCHEDULE.json').read_text())
for row in s['preflight_extension']+[{**r,'kind':'audit','target':r['mode']}for r in s['scopes']]:
 r=subprocess.run([sys.executable,str(E/'NNL_run.py'),row['attempt'],row['kind'],row['target']])
 if r.returncode:sys.exit(r.returncode)
