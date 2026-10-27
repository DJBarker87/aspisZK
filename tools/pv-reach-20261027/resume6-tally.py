from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume6'
rows=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-[0-9]*.json'))];accepted=[r for r in rows if r['accepted']];names=set();bad=[];contexts=[]
for r in accepted:
 for s in r['axioms']:
  n=re.match(r"'([^']+)'",s)[1];names.add(n)
  if '[' in s:
   xs=re.search(r'\[(.*?)\]',s,re.S)[1].replace('\n','').replace(' ','').split(',')
   if set(xs)-{'propext','Classical.choice','Quot.sound'}:bad.append(dict(attempt=r['attempt'],line=s))
 text=(E/f'out-{r["attempt"]}.log').read_text()
 for m in re.finditer(r'^COMPOSED_CONTEXT_LEAF (.+) after ([0-9]+): (.+)$',text,re.M):
  contexts.append(dict(attempt=r['attempt'],target=r['target'],owner=m[1],prefix_length=int(m[2]),callee=m[3]))
(E/'receipt-index.json').write_text(json.dumps(rows,indent=2)+'\n');(E/'source-context-leaves.json').write_text(json.dumps(contexts,indent=2)+'\n')
current=[]
for r in accepted:
 p=R/'docs/research/v8-r0-zk-20261009/lean'/(r['target']+'.lean')
 if p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']:current.append(dict(module=r['target'],attempt=r['attempt'],path=str(p.relative_to(R)),sha256=r['source_sha256']))
(E/'accepted-source-pins.json').write_text(json.dumps(current,indent=2)+'\n')
stats=dict(budget=100,submitted=[r['attempt'] for r in rows],charged=sum(r['exit'] is not None for r in rows),accepted=len(accepted),failed=[r['attempt'] for r in rows if not r['accepted']],unknown=[r['attempt'] for r in rows if r['exit'] is None],remaining=100-len(rows),refusals=len(list(E.glob('refusal-*.json'))),kani=0,unexpected_axioms=bad,distinct_accepted_axiom_names=len(names),max_peak_rss_bytes=max(r['peak_rss_bytes'] or 0 for r in rows),swaps=sorted({r['swaps'] for r in rows if r['swaps'] is not None}),full_invocation_coverage=False,minimal_reached_sets=False,native_nonvacuity=False)
(E/'budget.json').write_text(json.dumps(stats,indent=2)+'\n');print(json.dumps(stats));assert not bad
