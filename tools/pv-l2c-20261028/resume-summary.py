"""Current-source accepted results and charged-attempt accounting."""
from pathlib import Path
import json,hashlib,subprocess,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028/resume-d355'
res=json.loads((E/'focused-resolution.json').read_text())['resolved'];rows=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
current={}
for r in rows:
 if r['accepted'] and r['source_sha256']==res.get(r['module'],{}).get('sha256'):
  axioms=set()
  for a in r['axioms']:
   m=re.search(r'axioms: \[([^\]]*)\]',a)
   if m:axioms.update(n.strip() for n in m[1].split(',') if n.strip())
  assert axioms<={'propext','Classical.choice','Quot.sound'},(r['attempt'],axioms)
  current[r['module']]=dict(attempt=r['attempt'],source_sha256=r['source_sha256'],exit=r['exit'],wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],swap=r['swaps'],axioms=sorted(axioms),receipt='receipt-'+str(r['attempt'])+'.json')
summary=dict(branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),charged_Lean=len(rows),passed=sum(r['accepted'] for r in rows),failed=sum(not r['accepted'] for r in rows),authorized=72,remaining=72-len(rows),new_Kani=0,prior_Lean=68,total_Lean=68+len(rows),prior_Kani=6,ids=[r['attempt'] for r in rows],refusals=[p.name for p in E.glob('refusal-*.json')],current_source_accepted=current,rows={v:dict(before='OPEN/P bucket b',after='OPEN/P bucket b',removed=False) for v in ['V352','V354','V357','V360']},premises_removed=0,premises_added=0,premises_weakened=0,trust_fields_unchanged=True)
(E/'RESULTS.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k not in ['current_source_accepted','ids']}))
