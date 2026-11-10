#!/usr/bin/env python3
"""PCQH_mk_inputs.py: hand-written inputs for generator passes (preamble lemmas, fresh-namespace constant bindings, given proof blocks)."""
import json,sys
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent
(H/'inputs').mkdir(exist_ok=True)
P3B=(H.parent/'prov-p3b-20261109/PRVEq_AspisR72Sampler_Funs_P3.lean').read_text().split('\n')
def L(a,b): return '\n'.join(P3B[a-1:b])   # 1-based inclusive
# ---- R72: reuse the P3b proofs (same fresh text for M31.mul, CM31.*, QM31.*; checked by PCQH_mk_inputs.check below)
end_r23=next(i for i,l in enumerate(P3B,1) if l.strip()=='end PCVB_R23')
(H/'inputs/R72_preamble.lean').write_text(L(13,end_r23)+'\n')
m31=L(568,586); i0=m31.index('set_option') if m31.lstrip().startswith('set_option') else 0
qm_start=next(i for i,l in enumerate(P3B,1) if i>600 and l.strip()=='namespace AspisR72Sampler')
qm_end=next(i for i,l in enumerate(P3B,1) if i>qm_start and l.strip()=='#print axioms PRVEq.AspisR72Sampler.Funs.field.QM31.mul')
given={'field.M31.mul':L(568,586)+'\n\n'+L(588,591),'field.CM31.mul':L(623,626),'field.CM31.square':L(628,631),'field.QM31.mul':L(qm_start,qm_end)}
json.dump(given,open(H/'inputs/R72_given.json','w'),indent=1)
# ---- NFN: monadic M31 constants bound in the fresh namespace (recorded, CONDITIONAL_ON_BINDING) and the shift lemma
(H/'inputs/NFN_prelude.lean').write_text('''/- PRV constant binding (PCUH, recorded): the fresh emission types the cross-crate constants aspis_core.field.M31.ZERO/ONE as the external
   `Result M31` (FunsExternal_Template); the gate carries the pure constants. These two definitions instantiate the external with the gate
   value. Results that use them are CONDITIONAL_ON_BINDING until the constants' own fresh definition is shown equal. -/
def aspis_core.field.M31.ZERO : Result aspis_core.field.M31 := ok (_root_.NEW_GeometryActual.aspis_core.field.M31.ZERO)
def aspis_core.field.M31.ONE : Result aspis_core.field.M31 := ok (_root_.NEW_GeometryActual.aspis_core.field.M31.ONE)
''')
def fib(lab):
    q=f'NEW_GeometryActual.PRVFresh_{lab}.fast_domain.fibre_point'; g='NEW_GeometryActual.fast_domain.fibre_point'
    ql=f'NEW_GeometryActual.PRVFresh_{lab}.fast_domain.line_node'; gl='NEW_GeometryActual.fast_domain.line_node'
    one=f'NEW_GeometryActual.PRVFresh_{lab}.aspis_core.field.M31.ONE'
    E=f'PRVEq.{lab}.fast_domain'
    return {'fast_domain.fibre_point':f'''set_option maxHeartbeats 200000 in
/-- PCUH: fresh (checked `index >>> 9#i32`) = gate (`wrapping_shr index 9#u32`): the shift amount is in range (PRVH.usize_shr9). -/
theorem {E}.fibre_point : @{q} = @{g} := by
  delta {q} {g}
  simp only [PRVH.usize_shr9, {E}.TABLE_A, {E}.TABLE_B, {E}.table_value, lift]
#print axioms {E}.fibre_point''',
     'fast_domain.line_node':f'''set_option maxHeartbeats 200000 in
/-- PCUH: CONDITIONAL_ON_BINDING (the fresh namespace binds the external M31.ONE to the gate value, see NFN_prelude). -/
theorem {E}.line_node : @{ql} = @{gl} := by
  delta {ql} {gl} {one}
  simp only [{E}.fibre_point, bind_tc_ok]
#print axioms {E}.line_node'''}

def bpp(lab):
    ns=f'NEW_GeometryActual.PRVFresh_{lab}.verifier'; g='NEW_GeometryActual.verifier'; E=f'PRVEq.{lab}.verifier'
    return {'verifier.batch_prefix_products_loop.body':f'''set_option maxHeartbeats 200000 in
/-- PCUH: fresh checked `index + 1` = gate `wrapping_add index 1` because `index < flat.len` on the only path that reaches it (PRVH.usize_add_one_of_lt). -/
theorem {E}.batch_prefix_products_loop.body : @{ns}.batch_prefix_products_loop.body = @{g}.batch_prefix_products_loop.body := by
  funext flat prefixes product index
  delta {ns}.batch_prefix_products_loop.body {g}.batch_prefix_products_loop.body
  by_cases hlt : index < Slice.len flat
  · simp only [PRVH.usize_add_one_of_lt hlt, lift, bind_tc_ok]
  · simp [hlt]
#print axioms {E}.batch_prefix_products_loop.body''',
    'verifier.batch_prefix_products_loop':f'''set_option maxHeartbeats 200000 in
theorem {E}.batch_prefix_products_loop : @{ns}.batch_prefix_products_loop = @{g}.batch_prefix_products_loop := by
  funext flat prefixes product index
  delta {ns}.batch_prefix_products_loop {g}.batch_prefix_products_loop
  simp only [{E}.batch_prefix_products_loop.body]
#print axioms {E}.batch_prefix_products_loop'''}
json.dump(fib('NFN_ExtractedGeometry'),open(H/'inputs/NFN_given.json','w'),indent=1)
d2=fib('NFN_ExtractedGeometry_p2'); d2.update(bpp('NFN_ExtractedGeometry_p2'))
json.dump(d2,open(H/'inputs/NFN_p2_given.json','w'),indent=1)

def s1(lab='S1NativeCompactModelV1'):
    f=f'AspisS1NativeCompact.PRVFresh_{lab}.r1_wire'; g='AspisS1NativeCompact.r1_wire'; E=f'PRVEq.{lab}.r1_wire'
    return {'r1_wire.POINTS':f'''set_option maxHeartbeats 200000 in
/-- PCUH: the gate constant is the hand-written monadic `Result Usize := ok 3#usize`; the fresh constant is the pure `Usize`. The statement is therefore `ok fresh = gate` (not the plain fresh = gate shape). -/
theorem {E}.POINTS : (ok (@{f}.POINTS) : Result Std.Usize) = @{g}.POINTS := by
  delta {f}.POINTS {g}.POINTS
  rfl
#print axioms {E}.POINTS''',
    'r1_wire.CLAIMS':f'''set_option maxHeartbeats 200000 in
theorem {E}.CLAIMS : @{f}.CLAIMS = @{g}.CLAIMS := by
  delta {f}.CLAIMS {g}.CLAIMS
  rw [← {E}.POINTS]
  simp only [bind_tc_ok, {E}.LANES]
#print axioms {E}.CLAIMS'''}
json.dump(s1(),open(H/'inputs/S1_given.json','w'),indent=1)
print('ok',end_r23,qm_start,qm_end)
