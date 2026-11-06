from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for x in json.loads((E/'NLC_STEP_PLAN.json').read_text()):
 if (E/x['attempt']/'receipt.json').exists():
  assert json.loads((E/x['attempt']/'receipt.json').read_text())['exit_status']==0
  assert (E/x['attempt']/'sources/NLC_generated'/(x['module']+'.lean')).read_bytes()==(E/'NLC_generated'/(x['module']+'.lean')).read_bytes(), 'Stale source window receipt'
  continue
 subprocess.run([sys.executable,str(E/'NLC_config.py'),x['attempt'],x['module']],check=True)
 r=subprocess.run([sys.executable,str(E/'NLC_run.py'),x['attempt']])
 if r.returncode:sys.exit(r.returncode)
