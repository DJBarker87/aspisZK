import subprocess,json
from pathlib import Path
rows=json.loads(Path('evidence/pv-op223-20261027/extraction-split.json').read_text())['modules']
subprocess.run(['python3','tools/pv-op223-20261027/queue.py','R1Z/PV_Op223_Carrier',*[r['module'] for r in rows]],check=True)
