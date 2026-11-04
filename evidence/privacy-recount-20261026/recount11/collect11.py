from audit11 import *
old=json.loads((B/'recount10/definition-audit10.json').read_text()); rows=json.loads((B/'recount10/rows10.json').read_text())
out=[]
for r,d in zip(rows,old):
 assert r['id']==d['id'];w=[]
 paths=sorted({s['path'] for s in d['sources']}|{r.get('definition','').split('#')[0]})
 for k in revs:
  for p in paths:
   if not p:continue
   b=read(k,p)
   if b is not None:
    z=dict(manifest[k+':'+p]);z['prior_identical']=any(s['sha256']==z['sha256'] and s['path']==p for s in d['sources']);w.append(z)
 out.append({'id':r['id'],'sources':w,'changed':[z for z in w if not z['prior_identical']]})
(P/'definition-audit11.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
# Exact source/evidence input snapshots, no compiled objects or private corpora.
prefixes={'rw':['evidence/pv-rdcd5-20261101/','evidence/pv-rdcd7-20261102/'],
'uc':['evidence/pv-uc5-20261103/','evidence/pv-uc6-20261104/'],
'k3scan':['evidence/pv-k3scan3-20261104/'],
'evhc':['evidence/pv-evhc8-20261104/','evidence/pv-evhc9-20261104/'],
'stx':['evidence/pv-stx-20261104/'],
'evh':['evidence/pv-evh10-20261102/'], 'evhB':[],'b3p6':[],'runjoin':[]}
for k,prefs in prefixes.items():
 for p in tree(k):
  if any(p.startswith(t) for t in prefs) and p.endswith(('.md','.lean','.py','.rs','.toml','.lock','.json','.jsonl','.json.xz','.sha256','.txt','.log','.diff','.patch')):
   # Reuse huge historical reachable inventories via immutable git blobs; compact summaries suffice for recount.
   if any(t in p for t in ['REACHABLE','reachable/','COMBINED-SCAN-ROWS','NER_REBUILT_OBJECT_PINS']):continue
   read(k,p)
 # Read status documents even where jobs use an older evidence prefix.
 for p in tree(k):
  if p.startswith('evidence/pv-') and p.endswith(('/REPORT.md','/HANDOFF.md','/STATUS.md','/ROUTE.md','/BLOCKER-D588.md','/L3-RESIDUAL.md')):
   if k in ['evhB','b3p6','runjoin']:read(k,p)
for k in ['rw','uc']:
 for p in tree(k):
  if (p.startswith('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RDCD') or p.startswith('tools/r1-cost-probe/src/bin/user_client') or p.startswith('tools/pv-uc5-20261103/lean/')) and p.endswith(('.lean','.rs')):read(k,p)
for k in ['log','research']:
 for p in ['docs/research/v8-r0-zk-20261009/LOG.md','design/PV-OWNER-PACKET-20261027.md','evidence/axaudit2-20261102/NEP_Driver.lean','evidence/axaudit2-20261102/NEP_WALKER.lean']:read(k,p)
for p in ['evidence/pv-k3scan-20261101/CREDITS.json.xz','evidence/pv-k3scan-20261101/K3-ROWS.json','evidence/pv-k3scan-20261101/K3-CREDITS.md','evidence/pv-k3scan-20261101/K3-ROWS.md']:read('k3scan',p)
save(); print('definition rows',len(out),'changed',[(x['id'],len(x['changed'])) for x in out if x['changed']]);print('snapshots',len(manifest))
