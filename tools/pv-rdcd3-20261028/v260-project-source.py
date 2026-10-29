"""Complete Rust control/body patterns for the new V260 structural route.
This is not the unrecovered historical checker. Shared field calls are identical
Rust callees; their Aeneas agreement is existing tool trust, never premise removal.
Kernel proof receipts and the remaining library closure must also be present.
"""
from pathlib import Path
import json,hashlib,runpy,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
S=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028/src')
a=runpy.run_path(str(D/'v260-word-source.py'));span,tokens,sha=a['span'],a['tokens'],a['sha']
bundle=json.load(open(D/'v260-native-inputs.json'));records=[]
def text(path):
 j=bundle['files'][path];p=S/path;assert sha(p.read_bytes())==j['sha256'],path
 return p.read_text()
def check(path,context,marker,expected,law,differences):
 actual=span(text(path),context,marker)
 assert tokens(actual)==tokens(expected),(path,marker,actual)
 # A source constant change must fail this same complete-body check.
 bad=expected.replace('56','57',1) if '56' in expected else expected+' changed_body'
 assert tokens(actual)!=tokens(bad)
 records.append(dict(path=path,source_sha256=bundle['files'][path]['sha256'],context=context,body=actual,expected_body=expected,law=law,differences=differences,negative_control='changed complete body rejected'))
w='crates/aspis-r1-cost-probe/src/weights.rs';t='crates/aspis-r1-cost-probe/src/transport.rs';h='crates/aspis-r1-cost-probe/src/host_weights.rs';o='crates/aspis-core/src/r0/opening.rs'
check(w,'impl Weights {','pub fn raw(','''pub fn raw(&self,kind:usize,j:usize)->K {
 match kind {
  0=>if aspis_core::r0::opening::inactive(self.variant.row(j)).unwrap() {K::ONE} else {K::ZERO},
  4=>if j<56 {self.extra[j/28].pow((j%28) as u64)} else {K::ZERO},
  1..=3 if self.variant==Variant::D => {
   let r=self.variant.row(j);
   (0..10).fold(K::ONE,|v,b|v.mul(if r&(1<<b)==0 {K::ONE.sub(self.points[kind-1][9-b])}else{self.points[kind-1][9-b]}))
  },
  _=>{
   let k=if kind<4 {kind-1}else{kind-2};
   (0..5).fold(K::ONE,|v,d|v.mul(self.factors[k][d][(j>>(2*d))&3]))
  }
 }
}''','R1Z.PV_RDCD3_V260Exact.source; V260Folds tensor_loop/point_loop/point_read_order',[
 'Rust match guards versus nested conditions: V260Owned.source/variant_eq',
 'Source range/fold versus exact owned loop: Range194 and RangeLoop; fixed five/ten specialization: OrderedFold',
 'Immutable reads and copied values: Index194.frame and ReadHoist; complete failures/divergence retained',
 'Scalar/shift/cast bounds: V260Bounds and Word194',
 'No field arithmetic callee is replaced; both Rust bodies call the same aspis_core::field::QM31 methods'])
check(t,'impl Variant {','pub fn row(','''pub fn row(self,j:usize)->usize {
 if self==Self::D {return aspis_core::r0::transport::COEFFICIENT_TO_ROW[j] as usize;}
 let mut out=0;
 for d in 0..5 {out|=((j>>(2*d))&3)<<(2*TAU[d]);}
 out
}''','V260RowSource/V260RowRange/V260RowResult; Range194',[
 'for Range<usize> versus owned counter: next-state projection and fixed five source steps',
 'D table is bound entry-for-entry by v260-constants; all invalid indices retain the first array error'])
check(o,'pub fn inactive(','pub fn inactive(','''pub fn inactive(r:usize)->Result<bool,Error> {
 if r>=1024 {return Err(Error::IndexOutOfRange);}
 Ok((COPY_ACTIVE_ROW_MASKS[r/16]>>(r%16))&1==0)
}''','V260RowResult.complete/inactive_indices; V260Exact.inactive_refactor',[
 'Native Err/unwrap panic path is retained in the exact reference and proved unreachable after a successful row lookup',
 'Earlier D table error propagates before inactive is called; no admitted-index hypothesis is added'])
check(h,'fn host_row(','fn host_row(','''fn host_row(variant:Variant,j:usize)->usize {
 if let Variant::D=variant {return HOST_COEFFICIENT_TO_ROW[j] as usize;}
 let mut out=0usize;let mut d=0usize;
 while d<5 {
  out|=((j>>((2*d) as u32))&3)<<((2*crate::transport::TAU[d]) as u32);
  d+=1;
 }
 out
}''','V260RowSource source0/S1/S2; V260RowResult.complete',[
 'Both counts are below ten: casts to u32 retain values; no overflow or oversized shift',
 'Host table, native table and Lean table must all match'])
check(h,'fn raw_value(','fn raw_value(','''fn raw_value(weights:Weights,kind:usize,j:usize)->K {
 if kind==0 {
  let r=host_row(weights.variant,j);
  return if (aspis_core::r0::opening::COPY_ACTIVE_ROW_MASKS[r/16]>>(r%16))&1==0 {K::ONE}else{K::ZERO};
 }
 if kind==4 {
  if j<56 {return weights.extra[j/28].pow((j%28) as u64);}
  return K::ZERO;
 }
 if kind>=1 && kind<=3 && weights.variant==Variant::D {
  let r=host_row(weights.variant,j);
  return point_raw(weights.points[kind-1],r);
 }
 let k=if kind<4 {kind-1}else{kind-2};
 tensor_raw(weights.factors[k],j)
}''','V260Owned.source; V260Exact.refactor/source',[
 'Fixed Copy storage is projected field-for-field; this is a value/Result law, not binary/world refinement',
 'Hoisting does not erase invalid-dimension failures: ReadHoist.loop_nonempty at five/ten iterations'])
check(h,'fn point_factor(','fn point_factor(','''fn point_factor(point:K,r:usize,b:u32)->K {
 if r&(1usize<<b)==0 {K::ONE.sub(point)}else{point}
}''','V260Folds.point_read_order; Word194.boundedShl',[
 'The bit guard is pure; either source branch reads the same point; both field error and divergence are retained'])
point='fn point_raw(points:[K;10],r:usize)->K {let mut v=K::ONE;'+''.join(f'v=v.mul(point_factor(points[{9-b}],r,{b}));' for b in range(10))+'v}'
check(h,'fn point_raw(','fn point_raw(',point,'V260Folds.point_loop',[
 'Exactly ten calls, point indices 9 down to 0 and bit positions 0 through 9; no omitted/reordered field call'])
tensor='fn tensor_raw(factors:[[K;4];5],j:usize)->K {let mut v=K::ONE;'+''.join(f'v=v.mul(factors[{d}][(j>>{2*d}u32)&3]);' for d in range(5))+'v}'
check(h,'fn tensor_raw(','fn tensor_raw(',tensor,'V260Folds.tensor_loop',[
 'Exactly five calls, rows 0 through 4 and shifts 0,2,4,6,8; all inner indices are masked to two bits'])
# Both copies resolve K to exactly the same Rust field module, not an invented leaf.
assert 'field::{QM31 as K' in text(w)
assert 'field::{QM31,QM31 as K' in text(h)
assert 'type K' not in text(w) and 'type K' not in text(h)
for p in ['crates/aspis-core/src/field.rs','crates/aspis-core/src/field/ct.rs']:
 j=bundle['files'][p];assert sha((S/p).read_bytes())==j['sha256']
features=json.load(open(D/'deployed-client-features.json'))
core=[x for x in features if x['name']=='aspis-core'];assert core
assert all('ct-host-prover' in x['features'] and 'r0' in x['features'] for x in core)
assert all(x['profile']['debug_assertions'] is False and x['profile']['overflow_checks'] is False for x in features)
result=dict(source_revision=bundle['revision'],source_input_sha256=sha((D/'v260-native-inputs.json').read_bytes()),bodies=records,shared_field_callees='Original and copy both call aspis_core::field::QM31; the pinned Aeneas reference uses the same deployed ct helpers. Reliance on Aeneas agreeing with Rust semantics is reclassification within existing tool trust, never premise removal.',status='BODY PATTERNS CHECKED ONLY; whole-row credit requires all named proof receipts, complete concrete library disposition, static data and finite native association',original_checker='Not recovered; no pin/projection generator relabelled as an original checker',feature_graph_sha256=sha((D/'deployed-client-features.json').read_bytes()),endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[])
(D/'v260-project-source-result.json').write_text(json.dumps(result,indent=2)+'\n')
print('Eight complete original/reference Rust bodies matched; field calls share the frozen deployed backend; full row proof/disposition still required')
