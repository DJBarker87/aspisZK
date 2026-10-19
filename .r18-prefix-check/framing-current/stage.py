from pathlib import Path
import hashlib,json,shutil
here=Path(__file__).resolve().parent
w=Path('/home/dombarker/project-offloads/aspis-r1-r18-prefix-20261016/lean-bridge')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=json.loads((here/'framing-reuse-audit.json').read_text());pins={e['module']:e for e in json.loads((here/'current-source-pins.json').read_text())};copies=[]
assert len(d['modules'])==len(pins)==17
for m,e in d['modules'].items():
 receipt=Path(e['receipt']);r=json.loads(receipt.read_text());src=Path(e['source_snapshot']);obj=Path(e['object'])
 assert sha(receipt)==e['receipt_sha256'] and r['exit_status']==0
 assert sha(src)==e['source_sha256']==pins[m]['source_sha256']==r['source_sha256']
 assert sha(obj)==e['object_sha256']==r['output_sha256']
 for dep in r['direct_imports']:
  assert sha(Path(dep['object_path']))==dep['object_sha256'],(m,dep['module'])
  if dep['module'] in d['modules']:assert dep['object_sha256']==d['modules'][dep['module']]['object_sha256']
  else:assert dep['module'].startswith(('Mathlib.','Lean.')),dep['module']
 assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in r['axiom_reports'])
 for p,dest in [(src,w/'sources'/(m.replace('.','/')+'.lean')),(obj,w/'objects'/(m.replace('.','/')+'.olean')),(receipt,w/'framing-cache-provenance/receipts'/(m+'.json')),(src,w/'framing-cache-provenance/sources'/(m.replace('.','/')+'.lean'))]:
  assert not dest.exists() or sha(dest)==sha(p),str(dest)
  copies.append((p,dest))
for src,dest in copies:
 dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dest)
for name in ['framing-reuse-audit.json','current-source-pins.json','stage.py']:
 shutil.copy2(here/name,w/'framing-cache-provenance'/name)
manifest=json.loads((w/'input-manifest.json').read_text());manifest['current_framing_cache']={'inventory_sha256':sha(here/'framing-reuse-audit.json'),'current_source_pins_sha256':sha(here/'current-source-pins.json'),'source_revision':next(iter(pins.values()))['source_revision'],'module_count':17,'repaired_uniform_source_sha256':pins['AspisV8R19.UniformStateFirstHit']['source_sha256'],'old_bridge_objects_reused':False}
(w/'input-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('PASS:17 current-source receipt/output/direct-import pins; copied to private overlay only')
