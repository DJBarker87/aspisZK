"""Source group interpreter; every local raw row remains symbolic."""
from pathlib import Path
import sys
L=Path('evidence/pv-b3p6-20261028/lean')
def emit(p,s):
 if '--check' in sys.argv:assert p.read_text()==s,str(p)
 else:p.write_text(s)
head='''namespace PV_B3P_Association554227
open Aeneas Aeneas.Std PV_B3P_227 Result PV_B3P_Binding9227 PV_B3P_Association550227
set_option autoImplicit false
'''
s='import PV_B3P_RawSource550227\nimport PV_B3P_P227_03a\nimport Lean.Elab.Tactic.AsAuxLemma\n'+head+'''
def external_group_source554 (input : Array aspis_core.field.QM31 4#usize) :
    Result (Array aspis_core.field.QM31 4#usize) := do
  let limbs ← raw_input550 input
  let a ← Array.index_usize limbs 0#usize
  let b ← Array.index_usize limbs 1#usize
  let c ← Array.index_usize limbs 2#usize
  let d ← Array.index_usize limbs 3#usize
'''
for j in range(4):s+=f'  let r{j} ← raw_row550 a b c d {j}#usize\n  let q{j} ← reference_poseidon.extension_from_raw_limbs r{j}\n'
s+='  .ok (Array.make 4#usize [q0,q1,q2,q3] (by simp only [List.length_cons,List.length_nil]; rfl))\n'
s+='''
attribute [local irreducible] Aeneas.Std.bind Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 reference_poseidon.extension_from_raw_limbs
  U64.wrapping_add U64.wrapping_sub U64.wrapping_mul core.convert.num.FromU64U32.from

theorem external_group_reference554 (input : Array aspis_core.field.QM31 4#usize) :
    external_group_source554 input = reference_poseidon.external_group227 input := by
  unfold external_group_source554 reference_poseidon.external_group227
  rw [raw_input_continuation550]
'''
indent='  '
for n in range(8):s+=indent+'apply bind_equal9\n'+indent+f'intro input{n}\n'
s+=indent+'conv_lhs => simp only [four_index_zero550,four_index_one550,four_index_two550,four_index_three550,bind_tc_ok]\n'
for j in range(4):
 s+=indent+'as_aux_lemma =>\n';indent+='  '
 s+=indent+'rw [raw_row_continuation550]\n'
 for k in range(36):
  if j==0 and k in [0,2,4,6]:s+=indent+'conv_rhs => rw [four_index_'+['zero','one','two','three'][k//2]+'550,bind_tc_ok]\n'
  if k==18:s+=indent+'as_aux_lemma =>\n';indent+='  '
  s+=indent+'apply bind_equal9\n'+indent+f'intro row{j}cell{k}\n'
 s+=indent+'apply bind_equal9\n'+indent+f'intro output{j}\n'
s+=indent+'rfl\n\n#print axioms external_group_reference554\nend PV_B3P_Association554227\n'
emit(L/'PV_B3P_ExternalGroup554227.lean',s)
print('four symbolic raw rows and all four reconstructions emitted')
# Global sums and final add keep source arithmetic trees. During the immutable
# sum pass, repeated reads of each four column entries use the same snapshots.
s='import PV_B3P_FromFnFour550227\nimport PV_B3P_P227_02\nimport PV_B3P_DigestCpsEq9227\nimport Lean.Elab.Tactic.AsAuxLemma\n'+head
s+='''
def external_sums_source554 (state : Array aspis_core.field.QM31 16#usize) :
    Result (Array (Array U64 4#usize) 4#usize) := do
'''
for col in range(4):
 for limb in range(4):
  for row in range(4):
   if limb==0:s+=f'  let q{col}_{row} ← Array.index_usize state {4*row+col}#usize\n'
   s+=f'  let a{col}_{limb}_{row} ← reference_poseidon.extension_limbs q{col}_{row}\n'
   s+=f'  let b{col}_{limb}_{row} ← Array.index_usize a{col}_{limb}_{row} {limb}#usize\n'
   s+=f'  let c{col}_{limb}_{row} ← lift (core.convert.num.FromU64U32.from b{col}_{limb}_{row})\n'
   if row:s+=f'  let sum{col}_{limb}_{row} ← lift (U64.wrapping_add '+(f'c{col}_{limb}_0'if row==1 else f'sum{col}_{limb}_{row-1}')+f' c{col}_{limb}_{row})\n'
s+='  .ok (Array.make 4#usize [\n'
for col in range(4):s+='    Array.make 4#usize ['+','.join(f'sum{col}_{k}_3'for k in range(4))+'] (by simp only [List.length_cons,List.length_nil]; rfl)'+(','if col<3 else'')+'\n'
s+='  ] (by simp only [List.length_cons,List.length_nil]; rfl))\n'
s+='''
attribute [local irreducible] Aeneas.Std.bind Array.index_usize
  reference_poseidon.extension_limbs U64.wrapping_add core.convert.num.FromU64U32.from

theorem external_sums_reference554 (state : Array aspis_core.field.QM31 16#usize) :
    external_sums_source554 state = reference_poseidon.global_sums227 state := by
  unfold external_sums_source554 reference_poseidon.global_sums227
'''
ref=(L/'PV_B3P_P227_02.lean').read_text().split('def reference_poseidon.global_sums227',1)[1].split('  := do\n',1)[1].split('\n\n')[0]
import re
bs=[re.match(r'  let (\w+) ←',x)[1]for x in ref.splitlines()if re.match(r'  let (\w+) ←',x)]
indent='  '
for j,b in enumerate(bs):
 if j%16==0:s+=indent+'as_aux_lemma =>\n';indent+='  '
 s+=indent+'apply bind_equal9\n'+indent+'intro '+b+'\n'
s+=indent+'rfl\n\n#print axioms external_sums_reference554\nend PV_B3P_Association554227\n'
emit(L/'PV_B3P_ExternalSums554227.lean',s)
print('global sums independently generated; bounded proof steps',len(bs))
s='import PV_B3P_RawRowContinuation550227\nimport PV_B3P_P227_02\n'+head+'''
def external_add_source554 (value : aspis_core.field.QM31) (sums : Limbs64_550) :
    Result aspis_core.field.QM31 := do
  let limbs ← reference_poseidon.extension_limbs value
  let raw ← from_fn_four550 (fun limb => do
    let v ← Array.index_usize limbs limb
    let wide ← lift (core.convert.num.FromU64U32.from v)
    let sum ← Array.index_usize sums limb
    lift (U64.wrapping_add wide sum))
  reference_poseidon.extension_from_raw_limbs raw

attribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.extension_from_raw_limbs U64.wrapping_add core.convert.num.FromU64U32.from

theorem external_add_reference554 (value : aspis_core.field.QM31) (sums : Limbs64_550) :
    external_add_source554 value sums = reference_poseidon.add_global227 value sums := by
  simp only [external_add_source554,from_fn_four550,reference_poseidon.add_global227,
    PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms external_add_reference554
end PV_B3P_Association554227
'''
emit(L/'PV_B3P_ExternalAdd554227.lean',s)
s='import PV_B3P_ExternalGroup554227\nimport PV_B3P_ExternalSums554227\nimport PV_B3P_ExternalAdd554227\nimport PV_B3P_P227_03b\nimport PV_B3P_LinkDefinitions13227\nimport Lean.Elab.Tactic.AsAuxLemma\n'+head
s+='''
def external_source554 (state : Array aspis_core.field.QM31 16#usize) :
    Result (Array aspis_core.field.QM31 16#usize) := do
'''
old='state';n=0
for g in range(4):
 for k in range(4):s+=f'  let q{g}_{k} ← Array.index_usize {old} {g*4+k}#usize\n'
 s+=f'  let output{g} ← external_group_source554 (Array.make 4#usize ['+','.join(f'q{g}_{k}'for k in range(4))+'] (by simp only [List.length_cons,List.length_nil]; rfl))\n'
 for k in range(4):
  s+=f'  let out{g}_{k} ← Array.index_usize output{g} {k}#usize\n'
  n+=1;s+=f'  let state{n} ← Array.update {old} {g*4+k}#usize out{g}_{k}\n';old=f'state{n}'
s+=f'  let sums ← external_sums_source554 {old}\n'
for j in range(16):
 s+=f'  let value{j} ← Array.index_usize {old} {j}#usize\n'
 if j<4:s+=f'  let sum{j} ← Array.index_usize sums {j}#usize\n'
 s+=f'  let result{j} ← external_add_source554 value{j} sum{j%4}\n'
 n+=1
 s+=f'  let state{n} ← Array.update {old} {j}#usize result{j}\n';old=f'state{n}'
s+=f'  .ok {old}\n'
s+='''
attribute [local irreducible] Aeneas.Std.bind Array.index_usize Array.update
  reference_poseidon.external_group227 reference_poseidon.global_sums227 reference_poseidon.add_global227

theorem external_source_reference554 (state : Array aspis_core.field.QM31 16#usize) :
    external_source554 state = reference_poseidon.external_linear_lazy state := by
  unfold external_source554 reference_poseidon.external_linear_lazy
  simp only [external_group_reference554,external_sums_reference554,external_add_reference554]
'''
ref=(L/'PV_B3P_P227_03b.lean').read_text().split('def reference_poseidon.external_linear_lazy',1)[1].split('  := do\n',1)[1].split('\n\n')[0]
bs=[re.match(r'  let (\w+) ←',x)[1]for x in ref.splitlines()if re.match(r'  let (\w+) ←',x)]
indent='  '
for j,b in enumerate(bs):
 if j%16==0:s+=indent+'as_aux_lemma =>\n';indent+='  '
 s+=indent+'apply bind_equal9\n'+indent+'intro '+b+'\n'
s+=indent+'simp only [bind_tc_ok]\n'
s+='''
theorem external_source_link554 :
    PV_B3P_Links13227.PV_B3P_Link_poseidon_external_linear_lazy external_source554 :=
  funext external_source_reference554

#print axioms external_source_reference554
#print axioms external_source_link554
end PV_B3P_Association554227
'''
emit(L/'PV_B3P_ExternalSource554227.lean',s)
print('all sixteen output stores and four group stores retained')
