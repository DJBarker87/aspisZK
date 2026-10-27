from pathlib import Path
import json,re,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume3';rows=sorted([json.loads(p.read_text()) for p in E.glob('receipt-[0-9]*.json')],key=lambda r:r['attempt']);old=sorted([json.loads(p.read_text()) for p in (E.parent/'resume2').glob('receipt-[0-9]*.json')],key=lambda r:r['attempt']);bad=[];parsed=[]
for r in rows:
 out=(E/f'out-{r["attempt"]}.log').read_text();ax=[]
 for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([\s\S]*?)\]|does not depend on any axioms)",out):
  deps=[] if m[2] is None else [x.strip() for x in m[2].split(',')];ax.append(dict(theorem=m[1],axioms=deps))
  if set(deps)-{'propext','Classical.choice','Quot.sound'}:bad.append(dict(attempt=r['attempt'],theorem=m[1],axioms=deps))
 parsed.append(dict(attempt=r['attempt'],target=r['target'],exit=r['exit'],launcher_exit=r['launcher_exit'],wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],swaps=r['swaps'],source_revision=r['source_revision'],source_sha256=r['source_sha256'],source_snapshot=r['source_snapshot'],deps_fingerprint=r['deps_fingerprint'],accepted=r['accepted'],axioms=ax))
summary=dict(new_attempts=len(rows),prior_attempts=len(old),total=len(rows)+len(old),remaining=100-len(rows)-len(old),new_passed=sum(r['accepted'] for r in rows),new_failed=sum(not r['accepted'] for r in rows),prior_passed=sum(r['accepted'] for r in old),prior_failed=sum(not r['accepted'] for r in old),kani_attempts=0,ids=[r['attempt'] for r in rows],refusals=len(list(E.glob('refusal-*.json'))),max_peak_rss_bytes=max(r.get('peak_rss_bytes') or 0 for r in rows),swap_total=sum(r.get('swaps') or 0 for r in rows),nonstandard_axioms=bad,new_axiom_reports=sum(len(r['axioms']) for r in parsed))
(E/'receipt-index.json').write_text(json.dumps(parsed,indent=2)+'\n');(E/'budget.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2));assert not bad
