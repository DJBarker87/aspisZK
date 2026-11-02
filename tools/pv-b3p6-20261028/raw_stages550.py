"""Emit named small raw stages. Never unfold arithmetic or all raw cells."""
from pathlib import Path
import re
L=Path('evidence/pv-b3p6-20261028/lean')
head='''import PV_B3P_RawPack3550227
import PV_B3P_RawDebugLoops550227
import PV_B3P_FourIndex550227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
'''
attrs='''\nattribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 U64.wrapping_add U64.wrapping_sub U64.wrapping_mul
  core.convert.num.FromU64U32.from
'''
s=head+attrs
# Exactly one output's four callbacks; its arithmetic helper is opaque.
s+='''\ntheorem raw_row_continuation550 {α : Type} (a b c d : Limbs32_550) (output : Usize)
    (next : Limbs64_550 → Result α) :
    (do let row ← raw_row550 a b c d output; next row) = (do
'''
for limb in range(4):
 for row in 'abcd':
  s+=f'      let {row}{limb} ← Array.index_usize {row} {limb}#usize\n      let {row}{limb}w ← lift (core.convert.num.FromU64U32.from {row}{limb})\n'
 s+=f'      let r{limb} ← reference_poseidon.raw_limb227 output a{limb}w b{limb}w c{limb}w d{limb}w\n'
s+='''      next (Array.make 4#usize [r0,r1,r2,r3] (by simp only [List.length_cons,List.length_nil]; rfl))) := by
  simp only [raw_row550,from_fn_four550,raw_cell550,
    PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms raw_row_continuation550
end PV_B3P_Association550227
'''
(L/'PV_B3P_RawRowContinuation550227.lean').write_text(s)
# A separate suffix theorem is instantiated with the sixteen raw cell values.
p=L/'PV_B3P_P227_03d.lean';original=p.read_text();suffix=original[original.index('  let a24 ←'):original.index('\n\n\nend PV_B3P_227')]
values=[f'i{4+20*r+5*c}'for r in range(4)for c in range(4)]
assert all(re.search(r'\b'+v+r'\b',suffix)for v in values)
rows=[f'(Array.make 4#usize [{",".join(values[4*r:4*r+4])}] (by simp only [List.length_cons,List.length_nil]; rfl))'for r in range(4)]
code='''import PV_B3P_RawRowContinuation550227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
'''+attrs+'\ntheorem raw_suffix550 ('+' '.join(values)+''' : U64) :
    (do
'''+suffix+'\n    ) = (do\n      let bound ← reference_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND\n'
for j in range(4):code+=f'      let p{j} ← raw_pack{j}_550 '+ ' '.join(rows)+' bound\n'
code+='''      .ok (Array.make 4#usize [p0,p1,p2,p3] (by simp only [List.length_cons,List.length_nil]; rfl))) := by
  simp only [four_index_zero550,four_index_one550,four_index_two550,four_index_three550,
    bind_tc_ok,raw_pack0_value550,raw_pack1_value550,raw_pack2_value550,raw_pack3_value550]
  rfl

#print axioms raw_suffix550
end PV_B3P_Association550227
'''
(L/'PV_B3P_RawSuffix550227.lean').write_text(code)
print('raw row continuation and isolated suffix generated')
