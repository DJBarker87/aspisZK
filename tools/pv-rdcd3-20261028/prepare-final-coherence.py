"""Prepare source freeze and original per-attempt snapshots for final host check."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd3-20261028';out=E/'final-launch-snapshots';out.mkdir(exist_ok=True)
modules={}
for p in sorted(E.glob('lean-*/receipt.json')):
 j=json.loads(p.read_text())
 if j['exit']:continue
 assert hashlib.sha256((R/j['source_path']).read_bytes()).hexdigest()==j['source_sha256'],j['module']
 snap=E/j['dependencies_snapshot'];assert hashlib.sha256(snap.read_bytes()).hexdigest()==j['dependencies_sha256']
 (out/(str(j['attempt'])+'.json')).write_bytes(snap.read_bytes())
 modules[j['module']]={k:j[k] for k in ['attempt','source_path','source_sha256','source_blob','source_revision']}
(E/'final-coherence-inputs.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),modules=modules),indent=2)+'\n')
print(len(modules),'successful source/launch snapshots prepared')
