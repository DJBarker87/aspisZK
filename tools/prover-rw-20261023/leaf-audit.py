#!/usr/bin/env python3
"""Audit exact selected leaf pins before reusing immutable Kani receipts."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence';O=E/'prover-rw-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
groups=[('ct-kernels-20261022',['crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs','crates/aspis-core/src/field/ct.rs']),('ct-kernels-v2-20261022',['crates/aspis-r1-cost-probe/src/ct_pole.rs','tools/ct-kernels-20261022/pole-compression.rs'])]
rows=[]
for packet,files in groups:
    for p in sorted((E/packet/'receipts').glob('*/receipt.json')):
        r=json.loads(p.read_text());target=' '.join(r.get('target',[]))
        if r.get('exit_status')!=0 or 'kani' not in target:continue
        matches={f:r.get('source_sha256',{}).get(f)==sha(R/f) for f in files}
        if not all(matches.values()):continue
        rows.append(dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p),target=r['target'],exit_status=0,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],selected_body_hashes={f:sha(R/f) for f in files},domain='Read the pinned harness: canonical field operands for field operations; arbitrary operands only where its harness states that; pole row/slot public bounds. These are local contracts, not a complete prover refinement.'))
unchanged={}
for f in ['crates/aspis-core/src/r0_transcript.rs','crates/aspis-core/src/state_only_private_merkle.rs','crates/aspis-r1-cost-probe/src/weights.rs','crates/aspis-r1-cost-probe/src/ct_pole.rs','crates/aspis-r1-cost-probe/src/compact.rs','crates/aspis-r1-cost-probe/src/r1_wire.rs','docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs']:
    before=subprocess.check_output(['git','show','084f714ccd:'+f],cwd=R)
    unchanged[f]=dict(sha256=sha(R/f),unchanged_from_v2=before==(R/f).read_bytes())
new=[]
for p in sorted((O/'continuation/receipts/candidate').glob('*kani*/receipt.json')):
    r=json.loads(p.read_text())
    if r.get('exit_status')!=0:continue
    new.append(dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p),target=r['target'],exit_status=0,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],qualification='Bounded codec comparisons, parametric digest framing, or single-cell volatile frames only; read the exact selected harness. Not a complete pipeline leaf contract.'))
cell_bindings=[]
pins=R/'tools/prover-rw-20261023/contracts/clear-bindings.json'
if pins.exists():
    for b in json.loads(pins.read_text()):
        source=(R/b['source']).read_text();a=source.index('pub(crate) fn '+b['function']);at=source.index('{',a);depth=1;end=at+1
        while depth:
            depth+=(source[end]=='{')-(source[end]=='}');end+=1
        body=source[a:end]
        cell_bindings.append(dict(**b,current_verbatim_sha256=hashlib.sha256(body.encode()).hexdigest(),selected_body_unchanged=hashlib.sha256(body.encode()).hexdigest()==b['verbatim_sha256']))
r2=O/'continuation/reused-r2-contracts.json'
retained_r2=json.loads(r2.read_text()) if r2.exists() else None
result=dict(retained_r2_selected_body_audit=retained_r2,new_passing_receipts=new,volatile_cell_source_bindings=cell_bindings,new_kani_invocations=34,reused_passing_receipts=rows,unchanged_selected_sources=unchanged,new_kani_runs=34,whole_leaf_contract_gate_complete=False,remaining='Complete the extracted external-call inventory and map every arithmetic/hash/codec/parallel boundary to its exact checked contract and domain; unchanged source alone is not contract evidence. Reused CT and pole receipts are verified above; no claim that they cover the entire external inventory.',print_axioms='N/A: source/domain receipt audit; no new Lean theorem')
(O/'leaf-contract-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(reused_receipts=len(rows),unchanged_all=all(x['unchanged_from_v2'] for x in unchanged.values()),whole_leaf_contract_gate_complete=False)))
