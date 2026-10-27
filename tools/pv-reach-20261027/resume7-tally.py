from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume7'
rows=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-[0-9]*.json'))];accepted=[r for r in rows if r['accepted']];bad=[]
for r in accepted:
 for line in r['axioms']:
  if '[' in line:
   names={x.strip() for x in re.search(r'\[(.*?)\]',line,re.S)[1].split(',')}
   if names-{'propext','Classical.choice','Quot.sound'}:bad.append(dict(attempt=r['attempt'],line=line))
(E/'receipt-index.json').write_text(json.dumps(rows,indent=2)+'\n')
used=sorted(int(p.stem.split('-')[-1]) for p in E.glob('used-[0-9]*.json'))
stats=dict(budget=100,charged=len([r for r in rows if r['exit'] is not None]),accepted=len(accepted),failures=[r['attempt'] for r in rows if not r['accepted']],unknown=[r['attempt'] for r in rows if r['exit'] is None],used_ids=used,unlaunched_ids=[39406,39476],refusals=len(list(E.glob('refusal-*.json'))),kani=0,unexpected_axioms=bad,max_peak_rss_bytes=max(r['peak_rss_bytes'] or 0 for r in rows),swaps=sorted({r['swaps'] for r in rows if r['swaps'] is not None}),full_invocation_coverage=False,minimal_reached_sets=False,universally_excluded_entries=[],native_nonvacuity=False)
(E/'budget.json').write_text(json.dumps(stats,indent=2)+'\n');print(json.dumps(stats));assert not bad
