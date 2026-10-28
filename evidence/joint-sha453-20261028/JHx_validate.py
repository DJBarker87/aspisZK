"""Validate exact-source receipts and accepted axioms, without replaying Lean."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];L=R/'lean'
x=json.loads((E/'JHx_GENERATOR_CHECK.json').read_text());rows=[json.loads(s) for s in (E/'JHx_ATTEMPTS.jsonl').read_text().splitlines()];required=[m['module'] for m in x['computations']+x['manifest']+x['families']]+['JHx_Instance','JHx_Joint'];result=[]
for name in required:
 p=L/(name+'.lean');h=hashlib.sha256(p.read_bytes()).hexdigest();matches=[r for r in rows if r.get('source_hashes',{}).get(p.name)==h and r['exit_status']==0]
 if not matches:result.append(dict(module=name,passed=False,reason='no passing exact-source receipt'));continue
 r=matches[-1];axioms=r['print_axioms'];accepted={'propext','Classical.choice','Quot.sound'}
 for a in axioms:
  if 'does not depend on any axioms' in a:continue
  assert set(re.search(r'\[(.*?)\]',a)[1].split(', '))<=accepted,a
 assert axioms,(name,'no axioms audit')
 result.append(dict(module=name,passed=True,attempt=r['attempt'],source_sha256=h,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],axioms=axioms))
report=dict(passed=all(r['passed'] for r in result),normal_attempts=sum(r['mode']!='large' for r in rows),agg16_attempts=sum(r['mode']=='large' for r in rows),results=result)
assert report['normal_attempts']<=60 and report['agg16_attempts']<=2
(E/'JHx_VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(passed=report['passed'],compiled=sum(r['passed'] for r in result),required=len(result),normal_attempts=report['normal_attempts'],agg16_attempts=report['agg16_attempts'])))
