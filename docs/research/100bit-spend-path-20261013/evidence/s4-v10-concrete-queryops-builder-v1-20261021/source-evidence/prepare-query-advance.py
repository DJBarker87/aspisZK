#!/usr/bin/env python3
from pathlib import Path
import re,json,hashlib,sys
B=Path(__file__).resolve().parents[3];E=B/'evidence/stage2-continuation-20261020';raw=(E/'generated/AspisR1Stage2/Funs.lean').read_text()
def item(name):
 a=raw.index('def '+name+'\n');return raw[a:raw.index('\n/--',a)]
a=item('verifier.accumulate_batched_with_node');in_place='def verifier.candidate.query_values_in_place\n' in raw
qname='verifier.candidate.query_values_in_place' if in_place else 'verifier.candidate.query_values'
q=item(qname);w=item('verifier.candidate.query_values') if in_place else '';original=a+'\n'+q+'\n'+w
s=a.replace('def verifier.accumulate_batched_with_node\n','def verifier.accumulateWithOps\n  (ops : AccumulateOps)\n')
for old,new in [('verifier.accumulate_batched_with_node_loop0','ops.basisLoop'),('verifier.accumulate_batched_with_node_loop1','ops.weightLoop'),('aspis_core.field.M31.ZERO','ops.zero'),('aspis_core.field.M31.ONE','ops.one'),('aspis_core.field.wide_exact.WideExact.mul_qm31','ops.mulE'),('aspis_core.field.wide_exact.WideExact.add','ops.addE'),('aspis_core.field.QM31.mul','ops.mulK'),('trace.value','ops.trace')]:s=s.replace(old,new)
t=q.replace('def '+qname+'\n','def verifier.candidate.'+('queryInPlaceWithOps' if in_place else 'queryWithOps')+'\n  (aops : AccumulateOps) (ops : QueryOps)\n')
t,n=re.subn(r'core.array.from_fn 4#usize\s+verifier.candidate.query_values(?:_in_place)?.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact\s+q','ops.values q',t);assert n==1
t,n=re.subn(r'core.cmp.PartialEq.ne.trait_default\s+aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact\s+folded we5','ops.ne folded we5',t);assert n==1
for old,new in [('verifier.accumulate_batched_with_node','verifier.accumulateWithOps aops'),('verifier.candidate.opening','ops.opening'),('fast_dots.four_dots','ops.dots'),('verifier.QueryGeometry.for_query','ops.inverse'),('verifier.circle_fold_with_inverses','ops.circle'),('verifier.line_fold_with_inverses','ops.line'),('aspis_core.field.M31.mul','ops.mulM'),('aspis_core.field.M31.double','ops.doubleM'),('aspis_core.field.M31.ONE','ops.oneM'),('aspis_core.field.M31.sub','ops.subM'),('verifier.mark','ops.mark'),('trace.value','ops.trace')]:t=t.replace(old,new)
header='''import Stage2ContinuationQueryLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2
abbrev Stage2K := aspis_core.field.QM31
abbrev Stage2E := aspis_core.field.wide_exact.WideExact
abbrev Stage2M := aspis_core.field.M31
structure AccumulateOps where
  zero : Result Stage2M
  one : Result Stage2M
  basisLoop : Stage2M → Stage2M → Usize → Array Stage2M 256#usize → Usize → Result (Array Stage2M 256#usize)
  weightLoop : core.ops.range.Range Usize → alloc.vec.Vec Stage2K → Stage2K → Usize → verifier.BatchedWeights → Usize → Array Stage2M 256#usize → Result verifier.BatchedWeights
  mulE : Stage2E → Stage2K → Result Stage2E
  addE : Stage2E → Stage2E → Result Stage2E
  trace : U16 → Usize → Stage2E → Result Unit
  mulK : Stage2K → Stage2K → Result Stage2K
structure QueryOps where
  opening : Slice U8 → Usize → Result (Slice U8)
  dots : Slice U8 → Array Stage2E 29#usize → Result (Array Stage2E 4#usize)
  inverse : verifier.QueryGeometry → Usize → Result (Array Stage2M 5#usize)
  circle : Stage2E → Array Stage2E 4#usize → Array Stage2M 5#usize → Result Stage2E
  values : Slice U8 → Result (Array Stage2E 4#usize)
  ne : Stage2E → Stage2E → Result Bool
  line : Stage2E → Array Stage2E 4#usize → Array Stage2M 5#usize → Result Stage2E
  mulM : Stage2M → Stage2M → Result Stage2M
  doubleM : Stage2M → Result Stage2M
  oneM : Result Stage2M
  subM : Stage2M → Stage2M → Result Stage2M
  mark : Option (verifier.Phase → Result Unit) → verifier.Phase → Result Unit
  trace : U16 → Usize → Stage2E → Result Unit
'''
w=w.replace('def verifier.candidate.query_values\n','def verifier.candidate.queryWithOps\n  (aops : AccumulateOps) (ops : QueryOps)\n').replace('verifier.candidate.query_values_in_place proof','verifier.candidate.queryInPlaceWithOps aops ops proof')
result=header+s+'\n'+t+'\n'+w+'\nend AspisR1Stage2\n';p=B/'lean/Stage2ContinuationQueryAdvance.lean'
if '--check' in sys.argv:assert p.read_text().startswith(result)
else:
 if '--with-proof' in sys.argv:result+=(E/'harness/templates'/('query-advance-'+('borrowed' if in_place else 'owned')+'.lean.txt')).read_text()
 p.write_text(result)
sha=lambda x:hashlib.sha256(x.encode()).hexdigest()
(E/'proofs/query-advance-binding.json').write_text(json.dumps(dict(whole_accumulator_and_query_bodies=True,original_bodies_sha256=sha(original),parameterized_bodies_sha256=sha(s+'\n'+t+'\n'+w),scope='Universally quantified typed callees; actual next increment and both whole emitted bodies retained'),indent=2)+'\n')
