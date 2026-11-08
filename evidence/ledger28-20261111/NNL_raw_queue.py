from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for row in json.loads((E/'NNL_SCHEDULE.json').read_text())['scopes']:
 r=subprocess.run([sys.executable,str(E/'NNL_run.py'),row['attempt'],'audit',row['mode']])
 if r.returncode:sys.exit(r.returncode)
