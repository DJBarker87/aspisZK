from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for a,m in enumerate(json.loads((E/'NIY_UPPER_PORT_MODULES.json').read_text()),71):
 r=subprocess.run([sys.executable,str(E/'NIY_run.py'),f'NIY_L{a:03d}','lean',m])
 if r.returncode:sys.exit(r.returncode)
