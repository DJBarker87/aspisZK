from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(E/'NLC_run.py'),'NLC_L020'],check=True)
for x in json.loads((E/'NLC_FIELD_PLAN.json').read_text()):
 subprocess.run([sys.executable,str(E/'NLC_kconfig.py'),x['attempt'],x['harness']],check=True)
 # Every distinct field gets its paired control. A timeout has no credit.
 subprocess.run([sys.executable,str(E/'NLC_run.py'),x['attempt']])
