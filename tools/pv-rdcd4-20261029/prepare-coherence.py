"""Prepare source freeze and original per-attempt snapshots for final host check."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029';out=E/'final-launch-snapshots';out.mkdir(exist_ok=True)
modules={}
for p in sorted(E.glob('lean-*/receipt.json')):
 j=json.loads(p.read_text())
 if j['exit']:continue
 assert hashlib.sha256((R/j['source_path']).read_bytes()).hexdigest()==j['source_sha256'],j['module']
 snap=E/j['dependencies_snapshot'];assert hashlib.sha256(snap.read_bytes()).hexdigest()==j['dependencies_sha256']
 (out/(str(j['attempt'])+'.json')).write_bytes(snap.read_bytes())
 modules[j['module']]={k:j[k] for k in ['attempt','source_path','source_sha256','source_blob','source_revision']}
extra=[]
leaf=E/'v220-library-sources.json'
if leaf.exists():
 for x in json.load(open(leaf)):extra.append(dict(path=x['path'],sha256=x['sha256']))
 for source in ['crates/aspis-core/src/field.rs','crates/aspis-core/src/field/ct.rs','crates/aspis-core/src/state_only_sumcheck.rs']:
  b=subprocess.check_output(['git','show','HEAD:'+source],cwd=R)
  extra.append(dict(path='/home/dombarker/project-offloads/codex-pv-fscan-20261028/src/'+source,sha256=hashlib.sha256(b).hexdigest()))
(E/'final-coherence-inputs.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),modules=modules,additional_native_source_pins=extra),indent=2)+'\n')
print(len(modules),'successful source/launch snapshots prepared')
