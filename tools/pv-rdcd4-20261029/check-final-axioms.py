from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029';allowed={'propext','Classical.choice','Quot.sound'}
checks=[]
for n in [66397,66398,66399]:
 p=E/f'lean-{n}/receipt.json';j=json.load(open(p));assert j['exit']==0,(n,j['exit'])
 found=set()
 for line in j['axioms']:
  m=re.search(r'depends on axioms:\s*\[([^\]]*)\]',line)
  if m:found.update(x.strip() for x in m[1].split(',') if x.strip())
 assert not found-allowed,(n,found-allowed)
 checks.append(dict(attempt=n,target=j['target'],exit=j['exit'],wall=j['wall'],peak_rss_kib=j['peak_rss_kib'],swap=j['swap'],source_revision=j['source_revision'],printed_declarations=len(j['axioms']),axioms=sorted(found)))
(E/'final-axioms-summary.json').write_text(json.dumps(dict(allowed=sorted(allowed),checks=checks),indent=2)+'\n');print('All final audit/replay axioms are within the three standard axioms.')
