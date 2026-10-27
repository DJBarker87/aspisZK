"""Emit named bit-clear theorem applications; no arithmetic recurrence reduction."""
from pathlib import Path
P=Path(__file__).resolve().parent;R=P.parents[1]
roots=[6144,6145,4097,2048,2049,1749,26214]
masks=set()
for m in roots:
 while m:
  masks.add(m);m=m&(m-1)
out='''import FJk_MaskValueStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_MaskValues
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical)
open FJk_MaskValueStep (model)
'''
for m in sorted(masks):
 bits=[j for j in range(16) if m>>j&1];i=bits[0];next_m=m&(m-1);tail=bits[1:]
 out+=f'''theorem m{m} (a : Array field.QM31 16#usize) (ha : canonical a)
    (sum out : field.QM31) (hs : Canon sum)
    (run : selector_mask_sum_16_loop a {m}#u16 false sum=ok out) :
    Canon out ∧ decode out=model a {bits} (decode sum) := by
  exact FJk_MaskValueStep.value a sum out {m}#u16 {m-1}#u16 {next_m}#u16 {i}#u32 {i}#usize {tail}
    ha hs (by decide) (by decide) rfl (by apply UScalar.eq_of_val_eq;scalar_tac) rfl rfl
    (fun s hs r=>'''+(f'm{next_m} a ha s out hs r' if next_m else 'FJk_MaskValueStep.zero a s out hs r')+''') run
'''+f'#print axioms m{m}\n'
for m in roots:
 bits=[j for j in range(16) if m>>j&1]
 out+=f'''theorem s{m} (a : Array field.QM31 16#usize) (ha : canonical a) (out : field.QM31)
    (run : selector_mask_sum_16 a {m}#u16=ok out) :
    Canon out ∧ decode out=model a {bits} 0 := by
  have factor : selector_mask_sum_16 a {m}#u16=selector_mask_sum_16_loop a {m}#u16 false field.QM31.ZERO := rfl
  rw [factor] at run
  simpa only [FIv_NativeValue.zero.2] using m{m} a ha field.QM31.ZERO out FIv_NativeValue.zero.1 run
#print axioms s{m}
'''
out+='end AspisR1.FJk_MaskValues\nend\n'
(R/'lean/FJk_MaskValues.lean').write_text(out)
