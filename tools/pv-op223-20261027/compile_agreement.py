import subprocess,json
from pathlib import Path
rows=json.loads(Path('evidence/pv-op223-20261027/extraction-split.json').read_text())['modules']
mods=['R1Z/PV_Op223_Agreement_'+r['declaration'].removeprefix('PV_Op223_Applied.aspis_core.field.').replace('.','_') for r in rows[:23]]
subprocess.run(['python3','tools/pv-op223-20261027/queue.py',*mods],check=True)
