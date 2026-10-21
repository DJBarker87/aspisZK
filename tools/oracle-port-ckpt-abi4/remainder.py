#!/usr/bin/env python3
"""Reproducible, field-specific remainder; no aggregate success assumption."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[2]
P=ROOT/'docs/research/100bit-spend-path-20261013'
OUT=P/'evidence/ckpt-abi4-20261021/remainder.json'
fields=[
 ('header',0,16,'variant=S2; next=10; status=1; reserved=0','reached TX1 split guard and query-loop next'),
 ('proofHash',16,32,'digest(proof)','entry proof suffix identity'),
 ('publicHash',48,32,'digest(public)','borrowed stage1 / reconstructed stage2 bytes; P2-prime'),
 ('state',80,32,'p.state','Prepared::new t.state; full transcript step order'),
 ('root0',112,32,'p.roots[0]','semantic Verified roots'),
 ('root1',144,32,'p.roots[1]','semantic Verified roots'),
 ('gamma',176,32,'p.gamma','Prepared::new scalar(27,y1,true)'),
 ('kappa',208,32,'p.kappa','Prepared::new scalar(28,inactive,false)'),
 ('alpha0',240,32,'p.alpha[0]','Prepared::new scalar(29,round0,false)'),
 ('alpha1',272,32,'p.alpha[1]','S2 scalar(30,folded_root ++ round1,false)'),
 ('rho',304,16,'p.rho','scalar_k(row+1,[]) and exact K representation'),
 ('queries',320,88,'p.queries','t.queries(row,final_message); ordered q/unique/bounded'),
 ('semanticAlpha',408,160,'p.semantic_alpha','sem.alpha and all ten K encodings'),
 ('coordinates',568,64,'p.z[0].x,y,p.z[1].x,y','sem.z in exact x0,y0,x1,y1 order'),
 ('claim',632,32,'p.claim','prepared_claim; actual powers/dots/semantic values'),
 ('rhs',664,32,'a.rhs','Accumulator::new and query_values steps 0..10'),
 ('power',696,16,'a.power','initial ONE and reached rho^10'),
 ('weights',712,1024,'a.weights','64 initial ZERO; lazy pending accumulation; pending.finish'),
 ('checksum',1736,32,'digest(domain ++ body)','immutable 1736 bytes and exact ordered hash call'),
]
modules=['OraclePortCkptAbi2Reached','OraclePortCkptAbiSourceFields','OraclePortCkptAbiSourceBacking','OraclePortCkptAbi3Sections','OraclePortCkptAbi2Extracted/Funs','OraclePortCheckpointAbiC5','OraclePortCheckpointResumeC5','OraclePortCheckpointStateC3','OraclePortFrozenOrderDecision','OraclePortFrozenOrderJoin','OraclePortFrozenOrderHeadline']
pins=[]
for name in modules:
    p=P/'lean'/(name+'.lean')
    if not p.exists(): raise SystemExit(str(p))
    pins.append(dict(path=str(p.relative_to(ROOT)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
body=dict(schema='checkpoint-abi4-precise-remainder-v1',source_pins=pins,
 fields=[dict(name=n,offset=o,width=w,source=s,provenance_required=r,complete_source_to_C5=False) for n,o,w,s,r in fields],
 remaining=[
 dict(id='reader-adoption',required='Instantiate resumeWithOps operations by actual emitted raw/e/k/query/semantic/weights operations. Construct fields and offsets with exact rejection Results, checked bounds and Box/allocation; fixed_composition atomic equalities are not discharged.',local_progress='Actual std shared interval and mutable next/back content laws; strict extracted decoder canonicality only.'),
 dict(id='extracted-byte-C5',required='Map U8/U32 and four/eight raw limbs to exact fields, identify all 18 body blocks plus checksum with body_byte and C5.encode at every bounded index. The pass-2 extraction is the sparse Rust reference, not a newly extracted full checkpoint/resume caller.',local_progress='Successful strict reference decoding yields canonical limbs; arbitrary writer raw limbs still cannot be quotiented without domain proof.'),
 dict(id='reached-prepared',required='Build Context from actual Rust sem/transcript/claims and prove it equals model prepared for accepted_inputs p,q,i. Context remains universally arbitrary in accepted_reference_resume.',owners='S1/S5/S9 preparation and transcript; checkpoint composes, does not redefine their models.'),
 dict(id='reached-accumulator',required='Initial 64 ZERO/rhs ZERO/power ONE/next0; simulate query_loop until next10 including lazy BatchedWeights, geometry, errors; prove pending.finish gives C3.write(model i.data rho q).accumulator.',owners='S7 query accumulation; S8/factored row/field owners; checkpoint composition.'),
 dict(id='allocation',required='For accepted-run refinement, connect successful try_reserve_exact/resize and Box construction to exact list contents and prove allocation errors cannot reach acceptance; unconditional allocator availability is not required. A separate claim about physical capacity/allocator/Drop needs richer operational state; content-only std state cannot recover requested capacity.',status='not supplied by existing std content model'),
 dict(id='callers',required='Typed frozen TX1/Pool TX2 source Calls, concrete Site/Signature, returned-state dependencies, ordinary errors, all six checkpoint reads interleaved after batch0 and before batch1. Current dV_frozen has no checkpoint stage: establish complete-program read accounting/transport before claiming AcceptedVerifierJoin.',status='source/CFG observation only'),
 dict(id='two-pass',required='AcceptedRunJoin.annotated exact enriched two-pass observation, or independent enrichment verdict stability plus raw join.',status='open; not implied by a successful fixture, writer proof, or single-pass result'),
 dict(id='runtime',required='Same account snapshot/proof suffix/public reconstruction and stage1 checkpoint adoption; P2/P2-prime retained.',status='separate unchanged obligation')],
 complete_checkpoint_cone=False,accepted_run_join=False,headline_premises_removed=0)
if '--check' in sys.argv:
    assert json.loads(OUT.read_text())==body
    print('Field and obligation pins unchanged; complete cone remains open')
else: OUT.write_text(json.dumps(body,indent=2)+'\n')
