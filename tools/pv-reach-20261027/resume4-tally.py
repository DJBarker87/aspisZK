from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume4';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
rows=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-[0-9]*.json'))]
accepted=[r for r in rows if r['accepted']];names=set();bad=[];contexts=[]
for r in accepted:
 for line in r['axioms']:
  if any(a not in ['propext','Classical.choice','Quot.sound'] for a in re.findall(r'\[(.*?)\]',line,re.S)[0].replace('\n','').replace(' ','').split(',')) if '[' in line else False:bad.append(dict(attempt=r['attempt'],line=line))
  m=re.match(r"'([^']+)'",line)
  if m:names.add(m[1])
 text=(E/f'out-{r["attempt"]}.log').read_text()
 for m in re.finditer(r'^COMPOSED_CONTEXT_LEAF (.+) after ([0-9]+): (.+)$',text,re.M):
  contexts.append(dict(attempt=r['attempt'],target=r['target'],owner=m[1],prefix_length=int(m[2]),callee=m[3]))
current={}
for r in accepted:
 p=R/'docs/research/v8-r0-zk-20261009/lean'/(r['target']+'.lean')
 if p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']:current[r['target']]=dict(module=r['target'],attempt=r['attempt'],source=str(p.relative_to(R)),source_sha256=r['source_sha256'])
(E/'receipt-index.json').write_text(json.dumps(rows,indent=2)+'\n')
(E/'accepted-source-pins.json').write_text(json.dumps(list(current.values()),indent=2)+'\n')
(E/'source-context-leaves.json').write_text(json.dumps(contexts,indent=2)+'\n')
budget=dict(budget=100,submitted_ids=list(range(37300,37335)),confirmed_scoped_results=sum(r['exit'] is not None for r in rows),accepted=len(accepted),failed_known=sum(not r['accepted'] and r['exit'] is not None for r in rows),unknown=[r['attempt'] for r in rows if r['exit'] is None],charged_conservatively=35,remaining_conservatively=65,kani=0,next_unused=37335,audit_ids=[37397,37398,37399],refusals=0,stopped='local-lean.txt rule 5: host SSH connection closed during receipt collection')
(E/'budget.json').write_text(json.dumps(budget,indent=2)+'\n')
stats=dict(receipts=len(rows),accepted=len(accepted),known_failures=budget['failed_known'],unknown=budget['unknown'],unique_accepted_axiom_reports=len(names),unexpected_axioms=bad,max_peak_rss_bytes=max(r['peak_rss_bytes'] or 0 for r in rows),recorded_swaps=sorted(set(r['swaps'] for r in rows if r['swaps'] is not None)),context_leaf_records=len(contexts),full_invocation_composition=False,final_audits_run=False,final_manifest_replayed=False)
(E/'stats.json').write_text(json.dumps(stats,indent=2)+'\n');print(json.dumps(stats));assert not bad
# Prepare, but never execute, the final three audit targets during the host stop.
mods=sorted(m for m in current if 'ComposedChunk' in m)
body='\n'.join('import '+m.replace('/','.') for m in mods)+'\n'
ctx_names=sorted(n for n in names if n.startswith('R1Z.PV_RE_ComposedContext.') and '.RealR1_client.' not in n and '.prover.prove_masked_retrying_with.' not in n)
auditA=body+'\n'.join('#print axioms '+n for n in ctx_names)+'\n'
auditB='import R1Z.PV_RE_ClientComposedContexts\nimport R1Z.PV_RE_OpaqueHashBoundary\n'+'\n'.join('#print axioms '+n for n in sorted(names) if '.RealR1_client.' in n or '.prover.prove_masked_retrying_with.' in n or n.startswith('R1Z.PV_RE_OpaqueHashBoundary.'))+'\n'
auditC='import R1Z.PV_RE_FinalAudit4A\nimport R1Z.PV_RE_FinalAudit4B\nimport R1Z.PV_RE_SourceContexts\n#print axioms R1Z.PV_RE_SourceContexts.context_failure\n#print axioms R1Z.PV_RE_SourceContexts.context_divergence\n'
manifest=[]
for label,s in [('A',auditA),('B',auditB),('C',auditC)]:
 p=R/'tools/pv-reach-20261027/drafts'/f'PV_RE_FinalAudit4{label}.lean.txt';p.write_text(s);manifest.append(dict(module=f'R1Z/PV_RE_FinalAudit4{label}',draft=str(p.relative_to(R)),sha256=hashlib.sha256(s.encode()).hexdigest(),compiled=False))
(E/'pending-audit-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
