"""Audit the completed pre-proof stages and the explicit timing stop."""
from pathlib import Path
import json,subprocess,hashlib
E=Path('evidence/pv-batch2-20261027');J=lambda p:json.loads((E/p).read_text())
assert J('ELF-GATE.json')['passed'];timing=J('timing-precheck/comparison.json');assert timing['alternating_pairs']==5 and not timing['passed']
runs=J('timing-precheck/runs.json');assert len(runs)==10 and all(x['exit_status']==0 for x in runs)
assert any(x['ratio']>1.03 for x in timing['results'])
assert J('SOURCE-IDENTITY.json')['passed']
for row in J('APPLIED.json')['files']:
 assert hashlib.sha256(Path(row['path']).read_bytes()).hexdigest()==row['sha256']
lib=Path('crates/aspis-r1-cost-probe/src/lib.rs').read_text()
assert '#[cfg(feature="prover")] mod host_sampler;' in lib and '#[cfg(feature="prover")] mod host_weights;' in lib
receipts=[]
for p in sorted(E.glob('candidate/*/receipt/receipt.json')):
 r=json.loads(p.read_text());assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']==0
 receipts.append(dict(path=str(p.relative_to(E)),**{k:r[k] for k in ['command','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','print_axioms']}))
assert len(receipts)==8,len(receipts)
for f in ['transfer','withdrawal']:
 for i in range(5):
  for who in ['baseline','candidate']:
   r=J(f'timing-precheck/{who}/sample-{i}/{f}-{100+i}/result.json');assert r['status']=='Ok'
rows=[]
for op,v,name in [(249,256,'gamma_sample'),(250,257,'ordinary_sample'),(251,258,'Weights.materialize'),(252,259,'Weights.new'),(253,260,'Weights.raw')]:
 rows.append(dict(op=op,row='V'+str(v),name=name,source_law='NOT ATTEMPTED: timing stop',copy_equality='NOT ATTEMPTED: timing stop',bridge='OPEN; original row unchanged'))
summary=dict(branch='codex/pv-batch2-20261027',base=timing['baseline_revision'],applied_revision=timing['candidate_revision'],stop='transfer indicative median +4.1491556% exceeds +3%; no extractor or Lean launch',elf_gate=True,timing=timing['results'],function_cost=J('function-cost-summary.json'),receipts=receipts,lean_attempts=0,lean_budget=100,kani_attempts=0,kani_budget=0,used_envj_ids=[],per_op=rows,fixture_byte_gate='NOT RUN: stopped before proof stage; successful proof generation and verification do not establish byte equality',formal_audit='NOT RUN; no new Lean theorem; #print axioms N/A',premises=dict(removed=[],retained=['V256','V257','V258','V259','V260','all existing endpoint and deployment hypotheses'],added_to_endpoint=[],changed_endpoint=[],transferred_to_T=[],trust_fields=['entropy_law','entropy_kernel','observation']),candidate_obligations='Each redirected copy needs complete Result, arbitrary-input observable/error equivalence, source/row bridge and native effect/side-channel binding; none discharged',target='not yet established',next_deliverable='Lead review of the timing stop and per-function costs; a revised authorized candidate must pass all three ELF pins and the same pre-check before extraction/proofs resume',keys='retained securely; no transactions or cleanup',cache='Pre-existing host compilation caches reused; no private target directory, Lean objects, or local target directory created')
(E/'FINAL.json').write_text(json.dumps(summary,indent=2)+'\n')
print('PASS: 3 ELF pins, 10 timing runs, 8 capped receipts; enforced +3% stop, 0 Lean / 0 Kani')
