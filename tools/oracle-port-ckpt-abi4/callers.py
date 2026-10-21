#!/usr/bin/env python3
"""Pin frozen caller excerpts. Source observations are not semantic joins."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
ROOT = Path(__file__).resolve().parents[2]
P = ROOT / 'docs/research/100bit-spend-path-20261013'
OUT = P / 'evidence/ckpt-abi4-20261021/callers.json'
SPECS = {
 'crates/aspis-r1-cost-probe/src/candidate.rs': ['prepare', 'query_loop', 'tx1', 'tx2_common', 'tx2_authenticated'],
 'crates/aspis-r1-cost-probe/src/verifier.rs': ['checkpoint', 'resume', 'read_checkpoint_weights'],
 'programs/r1-cost-probe/src/lib.rs': ['first_decoded'],
 'programs/r1-cost-probe/src/r1_pool_adapter.rs': ['stage1', 'stage2'],
 'crates/aspis-core/src/r0/heap.rs': ['filled'],
}
def sha(b): return hashlib.sha256(b).hexdigest()
def excerpt(path, name):
    data = (ROOT/path).read_bytes(); lines=data.decode().splitlines(keepends=True)
    start=next(i for i,s in enumerate(lines) if 'fn '+name+'(' in s or 'fn '+name+'<' in s)
    depth=0; opened=False
    for end in range(start,len(lines)):
        depth += lines[end].count('{')-lines[end].count('}')
        opened |= '{' in lines[end]
        if opened and depth==0: break
    body=''.join(lines[start:end+1])
    return dict(path=path,name=name,source_sha256=sha(data),first_line=start+1,last_line=end+1,excerpt_sha256=sha(body.encode()),body=body)
records=[excerpt(p,n) for p,ns in SPECS.items() for n in ns]
model='docs/research/100bit-spend-path-20261013/lean/OraclePortFrozenOrderDecision.lean'
m=(ROOT/model).read_text(); decision=m.split('def dV_frozen : Decision :=',1)[1].split('\ntheorem admitted',1)[0]
assert 'checkpoint' not in decision.lower() and 'resume' not in decision.lower()
assert 'slotPrograms p q slots' in decision
s10=P/'evidence/s10-inventory3-20261021'
reused=[dict(path=str(p.relative_to(ROOT)),sha256=sha(p.read_bytes())) for p in [s10/'ordering-facts.json',s10/'ordering-observations.json',s10/'generic-instantiation-review.json',s10/'STATUS.md']]
body=dict(schema='checkpoint-abi4-caller-observations-v1',records=records,reused_s10=reused,
 model=dict(path=model,sha256=sha((ROOT/model).read_bytes()),decision_excerpt_sha256=sha(decision.encode()),has_checkpoint_stage=False),
 tx1_order=['parse_shape','canonical_scan','prepare','Accumulator::new','batch_merkle(batch=0)','QueryGeometry::for_range(0,k)','BatchedWeights::new','query_loop(end=k)','pending.finish','checkpoint'],
 tx2_order=['resume','a.next == SPLIT guard','powers<29>','inactive decode','batch_merkle(batch=1)','QueryGeometry::for_range(next,22)','BatchedWeights::new','query_loop(end=22)','pending.finish','finish_relation'],
 checkpoint_reads=['proof','public','domain ++ body','proof','public','domain ++ body'],
 classification='source/CFG observations only; no typed source Calls or semantic joins',
 accepted_run_join=False,
 blockers=['The current dV_frozen decision has no checkpoint stage. A complete transport must account for the extra reads across the complete verifier, not delete them between unchanged batches.',
 'S10 pass 3 explicitly leaves typed source lowering, reachable instance/pointer-flow and semantic caller joins open.',
 'Stage 1 borrows public data; stage 2 reconstructs it. Cross-transaction equality is P2/P2-prime, not supplied by these source excerpts.'])
if '--check' in sys.argv:
    assert json.loads(OUT.read_text()) == body
    print('Caller/model/S10 pins unchanged; semantic joins remain open')
else:
    OUT.write_text(json.dumps(body,indent=2)+'\n')
