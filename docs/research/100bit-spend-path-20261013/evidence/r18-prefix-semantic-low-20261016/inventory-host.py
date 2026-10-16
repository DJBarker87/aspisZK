from pathlib import Path
import json,hashlib
base=Path('/home/dombarker/project-offloads')
w=base/'aspis-r1-r18-prefix-20261016/semantic-frontier'
rank=base/'aspis-r1-r18-sampler-rank-final-20261016'
mask=base/'aspis-r1-mask-lean432-20261015'
r17=base/'aspis-r1-j17-port-20261015/extracted'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
snap=json.loads((rank/'external-inputs-rank-final.json').read_text())
manifest=json.loads((rank/'sources/SOURCE-MANIFEST.json').read_text())
current={x['module']:x for x in json.loads((w/'current144-audit.json').read_text())['targets']}
old={};seen=set()
def walk(n):
 if n in seen:return
 seen.add(n)
 if n in manifest['modules']:
  x=manifest['modules'][n];deps=x['imports'];typ='fresh-rank'
 else:
  x=snap['modules'][n];deps=x['imports'];typ=x.get('root')
 if typ is None or n.startswith(('Mathlib','Lean','Init','Std','Batteries','Aesop','Qq','Plausible','ProofWidgets','ImportGraph','LeanSearchClient')):return
 for d in deps:walk(d)
 old[n]=x
walk('R0C.ModuloField')
selected={};issues=[];old_changes=[]
for n,x in old.items():
 if n=='R0C.ModuloField':continue
 if n in current:
  a=current[n];ps=list((mask/'attempts').glob(a['attempt']+'-*/receipt.json'));assert len(ps)==1
  rp=ps[0];r=json.loads(rp.read_text());src=Path(r['snapshot_path']);obj=Path(r['output_path'])
  assert r['exit_status']==0 and sha(src)==r['source_sha256']==x['source_sha256']==a['source_sha256']
  assert sha(obj)==r['output_sha256']==a['object_sha256']
  deps={i['module']:i['object_sha256'] for i in r['direct_imports']}
  selected[n]={'kind':'current144','source':str(src),'source_sha256':sha(src),'object':str(obj),'object_sha256':sha(obj),'receipt':str(rp),'receipt_sha256':sha(rp),'direct_import_objects':deps}
 elif (r17/'successful-targets'/(n+'.json')).exists():
  rp=r17/'successful-targets'/(n+'.json');r=json.loads(rp.read_text());src=r17/'sources'/(n.replace('.','/')+'.lean');obj=r17/'objects'/(n.replace('.','/')+'.olean')
  assert r['exit_status']==0 and r['axioms']['passed'] and sha(src)==r['key']['source_sha256']==x['source_sha256']
  assert sha(obj)==r['objects']['.olean']['sha256']
  deps={k:v['objects']['.olean']['sha256'] for k,v in r['key']['imports'].items()}
  selected[n]={'kind':'R17','source':str(src),'source_sha256':sha(src),'object':str(obj),'object_sha256':sha(obj),'receipt':str(rp),'receipt_sha256':sha(rp),'direct_import_objects':deps}
 else:
  src=Path(x['source']);obj=Path(x['objects']['.olean']['path']);assert sha(src)==x['source_sha256'] and sha(obj)==x['objects']['.olean']['sha256']
  deps={i:snap['modules'][i]['objects']['.olean']['sha256'] for i in x['imports']}
  selected[n]={'kind':'rank-reviewed-pure-cache','source':str(src),'source_sha256':sha(src),'object':str(obj),'object_sha256':sha(obj),'rank_snapshot':str(rank/'external-inputs-rank-final.json'),'rank_snapshot_sha256':sha(rank/'external-inputs-rank-final.json'),'direct_import_objects':deps}
 if 'objects' in x and x['objects']['.olean']['sha256']!=selected[n]['object_sha256']:old_changes.append(n)
for n,x in selected.items():
 for d,h in x['direct_import_objects'].items():
  if d in selected and selected[d]['object_sha256']!=h:issues.append({'module':n,'dependency':d,'expected':h,'selected':selected[d]['object_sha256']})
report={'scope':'Read/hash-only selection. No objects copied, source modified, or compilation performed. Preserve original rank receipts.','modules':selected,'changed_object_selection_from_rank':old_changes,'direct_import_object_mismatches':issues,'proposed_missing_targets':['R0C.ModuloField']+[x['module'] for x in json.loads((w/'target-source-pins.json').read_text())]}
(w/'inventory.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'selected':len(selected),'changed':old_changes,'mismatches':issues,'next':report['proposed_missing_targets']},indent=2))
