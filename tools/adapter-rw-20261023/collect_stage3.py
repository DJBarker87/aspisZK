"""Host-side small artifact/receipt collection; never exports binaries or LLBC."""
from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent;O=B/'export-stage3-final';O.mkdir(exist_ok=True)
for name in ['charon-005','charon-006','charon-007','charon-008','aeneas-004','aeneas-005','aeneas-006','aeneas-007']:
 p=B/name;q=O/name;q.mkdir(exist_ok=True)
 for f in ['receipt.json','stdout.log','time.log']:
  if (p/f).exists():(q/f).write_bytes((p/f).read_bytes())
 for f in [name+'.json',name+'-reservation.json']:
  if (B/f).exists():(O/f).write_bytes((B/f).read_bytes())
files=[*(B/'generated-v6/AdapterRw').glob('*.lean'),B/'AdapterRw.llbc',B/'generated-final/translation.json',B/'generated-v5/translation.json',B/'generated-v6/translation.json',*B.glob('AdapterRw*.olean')]
for name in ['charon-008','aeneas-007']:
 x=json.loads((B/(name+'.json')).read_text());files.append(Path(x['command'][0]))
(O/'artifact-pins-final.json').write_text(json.dumps({str(p):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in files},indent=2)+'\n')
