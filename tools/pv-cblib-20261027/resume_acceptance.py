"""Distinguish exit-zero diagnostics from standard-axiom proof acceptance."""
from pathlib import Path
import json,re,hashlib
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027';t=json.loads((out/'TALLY.json').read_text());records=[]
for a in t['lean_charged']:
 r=json.loads((out/f'{a}.json').read_text());bad=[]
 for line in r.get('axioms',[]):
  m=re.search(r'depends on axioms: \[([^\]]*)\]',line,re.S)
  if m:bad += [s.strip() for s in m[1].split(',') if s.strip() not in ['propext','Classical.choice','Quot.sound']]
 p=root/'docs/research/v8-r0-zk-20261009/lean'/(r['module']+'.lean')
 current=p.exists() and hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']
 records.append(dict(attempt=a,module=r['module'],exit=r['exit'],bad_axioms=bad,current_source=current,accepted=r['exit']==0 and not bad))
(out/'RESUME-ACCEPTANCE.json').write_text(json.dumps(records,indent=2)+'\n')
print('accepted',sum(x['accepted'] for x in records),'of',len(records),'historical compiles; current accepted modules',len({x['module'] for x in records if x['accepted'] and x['current_source']}))
