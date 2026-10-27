#!/usr/bin/env python3
"""Read-only RunJoin source/receipt pinning for the mathematical parent consumer."""
import pathlib,subprocess,json,hashlib,re
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
rev=subprocess.check_output(['git','rev-parse','codex/pv-runjoin-20261026'],text=True).strip()
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'evidence'],text=True).splitlines()
receipts=[]
for path in paths:
 if not (re.search(r'/receipt-\d+\.json$',path) or path.endswith('/attempts.jsonl')):continue
 if 'pv-runjoin' not in path:continue
 b=subprocess.check_output(['git','show',rev+':'+path])
 try:data=[json.loads(l) for l in b.splitlines()] if path.endswith('.jsonl') else [json.loads(b)]
 except (ValueError,TypeError):continue
 for r in data:
  if not isinstance(r,dict):continue
  m=(r.get('target') or r.get('module') or '').replace('/','.')
  if m.startswith('PV_'):m='R1Z.'+m
  receipts.append((m,path,r))
rows=[]
for m in sorted({m for m,_,_ in receipts if 'RootModel' in m or m in {'R1Z.PV_RunJoin_FixtureRecords','R1Z.PV_RunJoin_ShippedExternal'}}):
 source='docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean'
 b=subprocess.check_output(['git','show',rev+':'+source]);sha=hashlib.sha256(b).hexdigest()
 good=[(p,r) for mm,p,r in receipts if mm==m and r.get('source_sha256')==sha and (r.get('exit')==0 and (r.get('accepted') or r.get('validation_exit')==0) or r.get('exit')==['exit=0'])]
 assert good,m
 p,r=good[-1]
 names={n.strip() for a in r.get('axioms',[]) for g in re.findall(r'depends on axioms: \[([^\]]*)\]',a) for n in g.split(',') if n.strip()}
 assert names <= {'propext','Classical.choice','Quot.sound'},(m,names)
 (e/('resume9-model-receipt-'+str(r['attempt'])+'.json')).write_text(json.dumps(r,indent=2)+'\n')
 rows.append(dict(module=m,source_path=source,source_sha256=sha,revision=rev,receipt=p,attempt=r['attempt'],object_sha256=r.get('object_sha256') or r.get('olean_sha256'),imports=re.findall(r'^import (\S+)',b.decode(),re.M)))

for row in rows:
 if not row['object_sha256']:
  for mm,pp,rr in receipts:
   dep=rr.get('dependencies',{}).get(row['module'])
   if dep and isinstance(dep,dict):row['object_sha256']=dep.get('sha256');row['object_hash_from_consumer_receipt']=pp;break

 if not row['object_sha256']:
  own=[json.loads(l) for l in (e/'resume9-attempts.jsonl').read_text().splitlines()]
  for rr in own:
   if not rr.get('accepted'):continue
   for dep in rr['dependency_objects']:
    if dep.endswith('/'+row['module'].replace('.','/')+'.olean'):
     row['object_sha256']=dep.split()[0];row['object_hash_from_own_focused_consumer']=rr['attempt'];break
   if row['object_sha256']:break
 assert row['object_sha256'],row['module']
assert len(rows)==25,(len(rows),[r['module'] for r in rows])
(e/'resume9-model-pins.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Read-only model and fixture pins',len(rows),rev)
