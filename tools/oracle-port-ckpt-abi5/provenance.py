#!/usr/bin/env python3
"""Reconcile frozen callers, kernel CFG witnesses and the new stage target.
This audit deliberately does not infer a semantic lowering from CFG paths.
"""
import hashlib,json,sys
from pathlib import Path
R=Path(__file__).resolve().parents[2]
P=R/'docs/research/100bit-spend-path-20261013'
E=P/'evidence/ckpt-abi5-20261021'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p): return dict(path=str(p.relative_to(R)),sha256=sha(p))
old=P/'evidence/ckpt-abi4-20261021/callers.json'
callers=json.loads(old.read_text())
for r in callers['records']:
 p=R/r['path'];assert sha(p)==r['source_sha256'],str(p)
 lines=p.read_text().splitlines(keepends=True)
 body=''.join(lines[r['first_line']-1:r['last_line']])
 assert body==r['body']
 assert hashlib.sha256(body.encode()).hexdigest()==r['excerpt_sha256']
s10=P/'evidence/s10-inventory4-20261021/dominance-map.json'
facts=json.loads(s10.read_text())['facts']
matched=[]
for f in callers['checkpoint_cfg']:
 matches=[d for d in facts if d['mode']==f['mode'] and d['body_sha256']==f['body_sha256']
          and d['before_block']==int(f['before']['block'][2:]) and d['after_block']==int(f['after']['block'][2:])]
 assert len(matches)==1
 d=matches[0];module=d['theorem'].split('.')[1]
 assert ('theorem '+d['theorem'].split('.')[-1]) in (P/'lean'/f'{module}.lean').read_text()
 matched.append(dict(mode=f['mode'],function=f['function'],body_sha256=f['body_sha256'],
  before_block=d['before_block'],after_block=d['after_block'],theorem=d['theorem']))
assert len(matched)==22
model=P/'lean/OraclePortFrozen2Decision.lean'
s=model.read_text()
assert 'bind (checkpoint stored p q tr i v)' in s
assert 'stage2 p q tr i a' in s
assert 'bind (batch p q batch0)' in s
assert 'bind (batch p q batch1)' in s
fields=json.loads((P/'evidence/ckpt-abi4-20261021/remainder.json').read_text())['fields']
for f in fields:
 f['complete_source_to_C5']=False
 if f['name'] in ['rho','semanticAlpha','coordinates','power','weights']:
  f['pass5_progress']='Canonical four-limb C5 representation; actual encode_k/body_byte and reached Rust operand adoption remain separate.'
result=dict(schema='checkpoint-abi5-provenance-v1',
 pins=[pin(x) for x in [old,s10,model,P/'lean/OraclePortFrozen2Checkpoint.lean',
  P/'lean/OraclePortFrozen2Join.lean',P/'lean/OraclePortStdAllocation.lean',
  P/'lean/OraclePortJoinSplitStdFrozen.lean',P/'evidence/s10-inventory4-20261021/STATUS.md',
  P/'evidence/ckpt-abi3-20261021/manifest.json',R/'tools/oracle-port-ckpt-abi3/reader-source.json']],
 cfg=matched,stage_has_checkpoint=True,ordered_reads=callers['checkpoint_reads'],
 reference_model_target='OraclePortCkptAbi5Decision.decision_observation',
 dynamic_counter_target=['OraclePortCkptAbi5Reached.tx1_next','OraclePortCkptAbi5Reached.tx2_next'],
 allocation_content_target='OraclePortCkptAbi5Weights.allocated_overwrite_exact',
 std_endpoint_boundary='S10 pass-4 acceptedRunJoin_of_cones targets the old frozen-order decision. Its generic std substitution and local filled contents are reused; no automatic endpoint transport to frozen2 is asserted.',
 source_model_classification='Model/reference equality only; CFG chronology and retained Kani are not a concrete source join.',
 fields=fields,
 remaining=[
  dict(id='reader-adoption',required='Identify the emitted current resume/Reader.k/e/semantic/weights call tree with the reference strict reader. Discharge ResumeOps atomic laws, exact Rust Result errors and immutable checkpoint/cursor law. Retained field-section Kani roots check the byte-exact excerpt under verified contracts, not linked full resume.'),
  dict(id='byte-identification',required='Relate actual extracted encode_k/e_byte/body_byte U8 results and production reader outputs to C5 for all 18 blocks plus checksum. Canonical raw-to-exact representation alone does not establish those function equations.'),
  dict(id='prepared-provenance',required='S1/S5/S9 must construct actual Rust Prepared fields from sem/transcript/claim and identify them with prepared(context p i v) i.data rho q. No arbitrary Context hypothesis remains in reached_stage, but this is model provenance only.'),
  dict(id='accumulator-provenance',required='The emitted WithOps successful query_loop now yields ten/twelve calls and exact next via checked query_next, without an advance hypothesis. Production call adoption, initial ZERO/ONE and pending.finish identification of rhs/power/64 weights with C3.write/run22 remain S7/S8 obligations. Static dominance cannot derive accumulated values.'),
  dict(id='allocation-correspondence',required='Instantiate S10 trustedStd filled reservation outcome from actual try_reserve_exact/resize; identify produced Vec length/content. Connect mutable writeback and fallible field reads to source read_checkpoint_weights. Box::new and physical allocator/Drop state remain a source operational boundary. Allocation failure must not reach acceptance; universal availability is not required.'),
  dict(id='caller-lowering',required='Construct concrete frozen TX1 and Pool TX2 Calls/carriers and source identity at the dV_frozen2 checkpoint position; preserve exact bytes, all errors and ordered reads. Then construct enriched observation identity for both annotation passes.'),
  dict(id='runtime',required='Retained StoredCarrierBinding/P2/P2-prime: checkpoint account, proof suffix and reconstructed public bytes belong to the same snapshot/transaction pair.')],
 complete_checkpoint_cone=False,accepted_run_join=False,headline_premises_removed=0)
out=E/'provenance.json'
if '--check' in sys.argv:
 assert json.loads(out.read_text())==result
 print('22 kernel CFG witnesses and current checkpoint-stage/caller pins match; semantic source remainder retained')
else:out.write_text(json.dumps(result,indent=2)+'\n')
