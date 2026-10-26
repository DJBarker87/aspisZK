from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent;R=E.parents[1];p=json.loads((E/'RPz3_source-plan.json').read_text());prior={}
for d in ['replay-dry2-20261026','replay-dry3-20261026']:
 for f in (R/'evidence'/d).glob('RPz*_*/receipt.json'):
  r=json.loads(f.read_text());m=r['module']
  if m in p['modules'] and not m.startswith(('RPz_Audit','RPz2_Audit')):prior[m]={'receipt':str(f.relative_to(R)),**r}
s={};invalid=[]
for m in p['order']:
 r=prior.get(m);x=p['modules'][m]
 if r:
  same=list(r['source_hashes'].values())==[x['sha256']]
  deps=all(p['modules'][n]['kind']=='trusted-library' or s.get(n)=='passed' for n in x['imports'])
  if r['exit_status']!=0 and same:s[m]='failed'
  elif same and deps:s[m]='passed'
  else:invalid.append(m)
(E/'RPz3_reuse.json').write_text(json.dumps({'state':s,'invalidated':invalid,'receipts':{m:prior[m]['receipt'] for m in s}},indent=2)+'\n')
print(collections.Counter(s.values()),'invalidated',len(invalid))
