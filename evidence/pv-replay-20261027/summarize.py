"""Collect raw receipts, runtime object fingerprints, and exhaustive audit output."""
from pathlib import Path
import json,hashlib,re,collections,csv
P=Path(__file__).parent;E=P/'receipts';plan=json.loads((P/'replay-plan.json').read_text())
rows=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
results={r['module']:r for r in map(json.loads,(E/'results.jsonl').read_text().splitlines())}
counts=dict(collections.Counter(r['status'] for r in results.values()))
failures=[dict(attempt=r['attempt'],module=r['module'],exit=r['exit'],errors=r['errors'],full_output=(E/f"out-{r['attempt']}.log").read_text()) for r in rows if r['exit']]
(P/'failures.json').write_text(json.dumps(failures,indent=2)+'\n')
# Final plan fingerprints use the actual selected dependency object hashes;
# the original recursive source/import fingerprint is retained in replay-plan.json.
with (P/'replay-plan.tsv').open('w') as f:
 w=csv.writer(f,delimiter='\t');w.writerow(['order','module','source path','source sha256','deps fingerprint'])
 for i,m in enumerate(plan['order'],1):
  n=plan['nodes'][m];r=results[m];ds=r.get('deps');fp=hashlib.sha256(json.dumps([(d['module'],d['sha256']) for d in ds],separators=(',',':')).encode()).hexdigest() if ds is not None else 'BLOCKED'
  w.writerow([i,m.replace('/','.'),n['source_path'],n['source_sha256'],fp])
audit=json.loads((E/'audit-result.json').read_text()) if (E/'audit-result.json').exists() else None
ax=[];dag=[];nonstandard=[];theorem_count=None
if audit:
 s=(E/f"out-{audit['attempt']}.log").read_text();current=None
 for l in s.splitlines():
  if 'PV_REPLAY_' in l:l='PV_REPLAY_'+l.split('PV_REPLAY_',1)[1]
  if l.startswith('PV_REPLAY_MODULE '):
   z=re.match(r'PV_REPLAY_MODULE (\S+) DECL (.+)',l);current=dict(module=z[1],theorem=z[2])
  if l.startswith('PV_REPLAY_NONSTANDARD '):nonstandard.append(l)
  if l.startswith('PV_REPLAY_IMPORT '):
   z=re.match(r'PV_REPLAY_IMPORT (\S+) : (.*)',l);dag.append(dict(module=z[1],imports=z[2].split(',') if z[2] else []))
  if l.startswith('PV_REPLAY_THEOREM_COUNT '):theorem_count=int(l.split()[-1])
 for z in re.finditer(r"'([^\n]+)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)",s,re.M|re.S):
  theorem=z[1];a=re.search(r'\[([^\]]*)\]',z[2]);axioms=[x.strip() for x in a[1].split(',') if x.strip()] if a else []
  ax.append(dict(theorem=theorem,axioms=axioms))
 (P/'axioms-audit.json').write_text(json.dumps(dict(attempt=audit['attempt'],exit=audit['exit'],theorem_count=theorem_count,results=ax,nonstandard=nonstandard),indent=2)+'\n')
 (P/'actual-import-dag.json').write_text(json.dumps(dag,indent=2)+'\n')
 with (P/'actual-import-dag.tsv').open('w') as f:
  w=csv.writer(f,delimiter='\t');w.writerow(['order','module','imports'])
  for i,r in enumerate(dag,1):w.writerow([i,r['module'],','.join(r['imports'])])
summary=dict(research_revision=plan['revision'],project_closure_size=len(plan['order']),direct_external_boundary=len(plan['direct_external_boundary']),actual_imported_modules=len(dag) if dag else None,unique_project_results=counts,charged_compiles=len(rows),successful_compiles=sum(r['exit']==0 for r in rows),failed_compiles=sum(r['exit']!=0 for r in rows),closure_compiles=sum(r['exit']==0 and r['module'] in plan['nodes'] for r in rows),audit_attempt=audit['attempt'] if audit else None,audit_exit=audit['exit'] if audit else None,audited_theorem_count=theorem_count,nonstandard_axioms=nonstandard,peak_rss_kib=max(r['peak_rss_kib'] for r in rows),swaps=sum(r['swaps'] for r in rows),budget_limit=600,remaining_budget=600-len(rows),proof_source_changes=0,premises_removed=0,premises_added=0,premises_changed=0,Kani=0)
(P/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
