"""Expected work: exact source checks and coherent object hashing, no arithmetic."""
from pathlib import Path
import subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
for name in ['library-source.py','v265-source.py','v265-fingerprint.py']:
 subprocess.run(['python3',str(D/name)],check=True)
files=['library-source-result.json','v265-source-result.json','v265-fingerprint-result.json']
j=dict(files={f:hashlib.sha256((D/f).read_bytes()).hexdigest() for f in files},scope='Complete changed static inverse/library proof closure; unchanged prior original-circle checker and native finite fixtures are reused at their recorded pins',pointer_kani='QUARANTINED, no Kani recredit',composition='Reclassification within existing compiler/Aeneas trust, zero endpoint premise removal')
(D/'v265-final-source-result.json').write_text(json.dumps(j,indent=2)+'\n');print('Static inverse/library source and coherent private DAG checked')
