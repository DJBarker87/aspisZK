from pathlib import Path
import json,re
E=Path(__file__).resolve().parent
allowed={'propext','Classical.choice','Quot.sound'};records=[]
for p in sorted(E.glob('NBX_L*/receipt.json')):
 r=json.loads(p.read_text());out=(p.parent/'stdout.log').read_text()
 blocks=[]
 for m in re.finditer(r"^'(.+)' (depends on axioms:\s*\[[\s\S]*?\]|does not depend on any axioms)",out,re.M):
  full=m.group(0);names=[]
  if 'depends on axioms:' in full:names=[s.strip() for s in full.split('[',1)[1].rsplit(']',1)[0].split(',') if s.strip()]
  blocks.append(dict(theorem=m.group(1),full=full,axioms=names,standard_only=set(names)<=allowed))
 records.append(dict(attempt=r['attempt'],module=r['module'],exit=r['exit_status'],accepted=r['exit_status']==0,axiom_blocks=blocks))
 if r['exit_status']==0:assert all(x['standard_only'] for x in blocks),(r['attempt'],blocks)
(E/'NBX_AXIOMS.json').write_text(json.dumps(records,indent=2)+'\n')
print('full multiline axiom audits',len(records),'all accepted standard-only')
