#!/usr/bin/env python3
"""Source-only provenance/receipt assembly; never a Lean or compatibility oracle."""
from pathlib import Path
import json,hashlib,subprocess,collections,shutil
R=Path(__file__).resolve().parents[2];E=R/'evidence/port18coherence-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean'
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def graph(a):
 p=E/a/'stdout.log'
 if not p.exists():p=Path('/tmp/port18coherence-large-evidence')/(a+'-stdout.log')
 d={}
 for line in p.read_text().splitlines():
  if line.startswith('EDGE '):m,n,ds=json.loads(line[5:]);d[n]=(m,ds)
 return d
root=graph('lean-011');candidate=graph('lean-012');orig={r['module']:r for r in json.loads((E/'original-root-objects.json').read_text())['objects']}
old=json.loads((R/'evidence/port17release-20261024/dependency-inventory.json').read_text())['selected']
raw=json.loads(Path('/tmp/port17release-local-dependencies.json').read_text())
transport=json.loads((E/'transport-manifest.json').read_text());snap={(r['side'],r['module']):r for r in transport['snapshots']}
names=[l[10:].strip() for l in (E/'lean-028/stdout.log').read_text().splitlines() if l.startswith('IDENTICAL ')]
assert len(names)==15241 and len(set(names))==15241
mods={};declarations=[]
for n in sorted(names):
 if n in root:side='root';m=root[n][0]
 elif n in candidate:side='candidate';m=candidate[n][0]
 else:
  assert n.startswith('AspisR1.Port17RELEASE_Driver.stages'),n
  side='candidate-extra';m='Port17RELEASE_Driver'
 declarations.append({'name':n,'origin':side+':'+m})
 if (side,m) in mods:continue
 s=snap[side,m];row={'side':side,'module':m,'transport_sha256':s['sha256'],'transport_bytes':s['bytes']}
 if side=='root':row['original_objects']=orig[m]['files']
 else:
  if m.startswith('Port17RELEASE_'):
   p=Path('/tmp/port17release-local-objects')/(m+'.olean')
   row['original_objects']=[{'path':str(p),'sha256':digest(p),'bytes':p.stat().st_size}]
  else:
   assert m in raw,m
   z=raw[m];p=Path(z['path']);assert digest(p)==z['sha256'],m
   row['original_objects']=[{'path':z['original'],'retained_view':str(p),'sha256':z['sha256'],'bytes':p.stat().st_size}]
 if side.startswith('candidate') and m in old and 'source_path' in old[m]:
  z=old[m];p=R/'evidence/port17release-20261024/dependency-source'/(m.replace('.','/')+'.lean');assert digest(p)==z['source_sha256']
  row['source']={'revision':'a4fa5c5ab357a4f6732a3e053965640c90a0df1e','path':z['source_path'],'owned_copy':str(p.relative_to(R)),'sha256':digest(p),'receipt':z['receipt'],'receipt_sha256':z['receipt_sha256'],'assessment':'Reused immutable committed source/receipt association; complete chosen terms newly kernel checked'}
 else:
  p=L/(m.replace('.','/')+'.lean')
  if p.exists():
   row['source']={'revision':'5544611e5fa592c7ca44ab12bf799618d8f773a4','path':str(p.relative_to(R)),'sha256':digest(p),'assessment':'Pinned root source bytes; existing source/object association reused, chosen declarations newly kernel checked. Not a new source-to-native/artifact identity gate.'}
  else:row['source']={'assessment':'Hashed external warm-cache logical baseline; original full source-module provenance/replay is not newly certified. All chosen expressions/types/bodies checked against the canonical environment; no native/IR association inferred.'}
 mods[side,m]=row
canonical={'schema':'port18-canonical-checked-declaration-closure-v1','status':'Checked logical declaration closure; not an untouched full module replay or native/release binding','root_proof_basis':'5544611e5fa592c7ca44ab12bf799618d8f773a4','immutable_A_basis':'a4fa5c5ab357a4f6732a3e053965640c90a0df1e','additional_A_deliveries_selected':[],'kernel_method':'Stock Lean.Replay traversal adapted to default kernel heartbeat limit and rejection of project axioms/unsafe/partial declarations; Kernel.Environment.addDeclCore, constructors/recursors regenerated and compared; no unchecked environment insertion','declarations':declarations,'modules':list(mods.values()),'fresh_project_declarations':10375,'matching_selected_declarations':15241,'source_vs_object_limit':'Object-term reconstruction preserves the selected source-model expressions. It does not certify every unused original module declaration, external textual-source provenance, elaborator extension/IR execution, native SDK/source binding, or frozen ELF identity.'}
b=(json.dumps(canonical,indent=2)+'\n').encode();assert len(b)<5000000
(E/'canonical-manifest.json').write_bytes(b)
receipts=[]
for p in sorted(E.glob('lean-*/receipt.json')):
 x=json.loads(p.read_text());x['receipt']=str(p.relative_to(R));receipts.append(x)
assert len(receipts)==29
actual=sum(x.get('kind')=='lean' for x in receipts);assert actual==26
summary={'schema':'focused-extractor-proof-packet-v1','base':'5544611e5fa592c7ca44ab12bf799618d8f773a4','inherited_charged':275,'inherited_actual_lean':273,'inherited_pre_lean_charges':2,'new_charged':29,'new_actual_lean':actual,'new_pre_lean_charges':3,'cumulative_charged':304,'cumulative_actual_lean':299,'cumulative_pre_lean_charges':5,'ceiling':356,'remaining':52,'kani':'0/20 unchanged','heavy_rust_backend_extraction':0,'full_frozen_manifest':False,'canonical_manifest_sha256':hashlib.sha256(b).hexdigest(),'canonical_manifest_bytes':len(b),'accepted_stages':{'domain':'lean-022','prepare':'lean-023','driver_effects':'lean-025','accounting':'lean-026','complete_statements_axioms_import_audit':'lean-028'},'prior_composition_status':'Port17 original mixed-cache composition WITHHELD; these receipts are new checked closure evidence only','receipts':receipts}
(E/'manifest.json').write_text(json.dumps(summary,indent=2)+'\n')
# Large derived JSON/JSON-lines logs stay external, hash+size only in git.
archive=Path('/tmp/port18coherence-large-evidence');archive.mkdir(exist_ok=True)
for p in E.glob('lean-*/stdout.log'):
 if p.stat().st_size>5000000:
  dest=archive/(p.parent.name+'-stdout.log');s=digest(p);size=p.stat().st_size
  (p.parent/'stdout-external.json').write_text(json.dumps({'sha256':s,'bytes':size,'retained_path':str(dest),'assessment':'Large derived structured output; hash+size only committed'},indent=2)+'\n')
  shutil.move(str(p),str(dest))
print(json.dumps({'canonical_bytes':len(b),'modules':len(mods),'declarations':len(names),'charged':304,'actual_lean':299,'remaining':52}))
