#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys
K=Path(__file__).resolve().parent
ROOT=K.parents[4]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
# Frozen and copied source pins.
frozen=ROOT/'crates/aspis-r1-cost-probe/src/verifier.rs'
assert sha(frozen)=='8c872d42bdaa245cc540be6b26d17108a5cb40754b8befb79e147f5843b1f756'
patch=K/'evidence/charon-v11/wrapper-delta.patch'
assert patch.is_file() and '+pub fn accumulator_new_probe(v: Variant)' in patch.read_text()
# Exact Charon output record: one ordinary wrapper root and one desired method.
llbc=K/'evidence/charon-v11/AccumulatorWrapper.llbc'
d=json.loads(llbc.read_text()); t=d['translated']
assert d['has_errors'] is False
assert len(t['fun_decls'])==20 and len(t['type_decls'])==13
funs=[f for f in t['fun_decls'] if f and f.get('item_meta')]
def name(f): return str((f.get('item_meta') or {}).get('name'))
ctor=[f for f in funs if 'pub fn new(v:Variant)' in ((f.get('item_meta') or {}).get('source_text') or '')]
assert len(ctor)==1
m=ctor[0]['item_meta']
assert m['opacity']=='Transparent' and m['span']['data']['beg']['line']==93
assert 'pub fn new(v:Variant)->Result<Self,Error>' in m['source_text']
assert any('accumulator_new_probe' in name(f) for f in funs)
assert not any('Prepared' in name(f) or 'Transcript' in name(f) for f in funs)
# Aeneas generated body preserves the exact fallible calls, map_err/Try branch,
# source field order and literal next=0. The generic theorem parameterizes these calls.
fp=K/'sources/AspisR1S4AccumulatorNewWrapperV11Probe/Funs.lean'
fs=fp.read_text(); start=fs.index('def verifier.Accumulator.new\n'); end=fs.index('/-- [aspis_r1_cost_probe::verifier::accumulator_new_probe]',start)
body=fs[start:end]
ordered=['transport.Variant.final_len v','aspis_core.field.QM31.ZERO','aspis_core.r0.heap.filled','core.result.Result.map_err','core.result.Result.Insts.CoreOpsTry.branch','core.ops.control_flow.ControlFlow.Continue val','aspis_core.field.wide_exact.WideExact.ZERO','aspis_core.field.QM31.ONE','weights := val, rhs := we, power := q1, next := 0#usize','core.ops.control_flow.ControlFlow.Break residual','CoreOpsTryTraitFromResidualResultInfallible.from_residual']
pos=-1
for token in ordered:
 q=body.find(token,pos+1); assert q>=0, f'missing/out-of-order emitted operation: {token}';pos=q
assert "Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 93:4-93:180" in fs[start-180:start]
# Exact result-valued model and caller adapter are the checked theorem sources.
model=(K/'sources/v3/AccumulatorNewEmittedSourceCutV3.lean').read_text()
caller=(K/'sources/v3/CallerStage2SourceConstructorV3.lean').read_text()
for token in ['(zeroQ : Result','(zeroWide : Result','(oneQ : Result','next := 0#usize','CoreOpsTry.branch','CoreOpsTryTraitFromResidualResultInfallible.from_residual','emittedBody_success_next_zero']:
 assert token in model,token
for token in ['withSourceAccumulatorNewResult','tx1_success_same_stage2_query','initialAcc.next = 0#usize']:
 assert token in caller,token
# Successful, source-pinned compiler receipts.
cr=json.loads((K/'evidence/charon-v11/receipt.json').read_text())
ar=json.loads((K/'evidence/aeneas-v11/receipt.json').read_text())
lr=json.loads((K/'evidence/lean-v2/source-cut-receipt.json').read_text())
wr=json.loads((K/'evidence/lean-v2/caller-receipt.json').read_text())
assert cr['exit_status']==0 and cr['translation_has_errors'] is False and cr['constructor_body_transparent'] is True
assert cr['output_sha256']==sha(llbc)
assert ar['exit_status']==0 and ar['llbc_sha256']==sha(llbc)
assert lr['exit_status']==0 and lr['object_sha256'] and wr['exit_status']==0 and wr['object_sha256']
# Ensure no compiled objects or Aeneas external templates are imported by theorem source.
assert 'import AspisR1S4AccumulatorNewWrapperV11Probe.Funs' not in model
vr=json.loads((K/'evidence/lean-v2/emitted-source-cut-v3-receipt.json').read_text())
vc=json.loads((K/'evidence/lean-v2/caller-v3-receipt.json').read_text())
assert vr['exit_status']==0 and vr['object_sha256']=='170a4488a5d1baa3132e7db0f8e4609dfa0d964cffef0318b7b09d6b62f17654'
assert vc['exit_status']==0 and vc['object_sha256']=='0dfb78c044c508270c2a7598c2e35fe62948af31c8a2f067046e957c787e875c'
assert 'depends on axioms: [propext,\n Classical.choice,\n Quot.sound]' in (K/'evidence/lean-v2/emitted-source-cut-v3-stdout.log').read_text()
assert 'depends on axioms: [propext,\n Classical.choice,\n Quot.sound]' in (K/'evidence/lean-v2/caller-v3-stdout.log').read_text()
print('PASS: frozen source pin, isolated transparent ctor extraction, generated body order, Result-valued source model and caller start-zero consumer')
