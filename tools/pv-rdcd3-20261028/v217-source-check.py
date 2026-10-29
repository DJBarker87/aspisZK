"""Expected phase: exact new source pattern matching, no arithmetic or compilation."""
from pathlib import Path
import subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
for name in ['v217-application-source.py','v217-field-source.py','v217-library-source.py']:
 subprocess.run(['python3',str(D/name)],check=True)
names=['v217-application-source-result.json','v217-field-source-result.json','v217-library-source-result.json']
j=dict(files={n:hashlib.sha256((D/n).read_bytes()).hexdigest() for n in names},scope='Changed source pattern checks only; no row status or machine semantics proof',composition='Existing Aeneas/Rust trust retained; endpoint premise changes zero')
(D/'v217-source-check-result.json').write_text(json.dumps(j,indent=2)+'\n')
