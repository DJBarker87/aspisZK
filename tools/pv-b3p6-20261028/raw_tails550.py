"""Split raw equality at each source row, retaining exact reference syntax.
Reference views only refactor pinned emission; native tails use independent
row/debug/packing interpreters. Each bridge opens at most one 40-bind row.
"""
from pathlib import Path
import re,json,hashlib
L=Path('evidence/pv-b3p6-20261028/lean');R=L.parent/'resume18';old=(L/'PV_B3P_P227_03d.lean').read_text()
body=old.split('  := do\n',1)[1].split('\n\n\nend PV_B3P_227')[0]
starts=[body.index('  let a4 ←'),body.index('  let i20 ←'),body.index('  let i40 ←'),body.index('  let i60 ←'),body.index('  let a24 ←')]
prefix=body[:starts[0]];chunks=[body[starts[i]:starts[i+1]]for i in range(4)]+[body[starts[4]:]]
vals=[f'i{4+20*r+5*c}'for r in range(4)for c in range(4)]
inputs=['a4','a6','a7','a8']
attrs='''\nattribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 U64.wrapping_add U64.wrapping_sub U64.wrapping_mul
  core.convert.num.FromU64U32.from
'''
header='''namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false
'''
s='import PV_B3P_RawSuffix550227\n'+header+attrs
# Reverse order makes each reference tail a single exact syntactic fragment.
for j in range(4,-1,-1):
 arrays=['a','a1','a2','a3']if j==0 else inputs if j<4 else[]
 params=(' ('+' '.join(arrays)+' : Limbs32_550)')if arrays else''
 if j:params+=' ('+' '.join(vals[:4*j])+' : U64)'
 s+=f'\ndef raw_reference_tail{j}_550'+params+' : Result Limbs64_550 := do\n'+chunks[j].rstrip()+'\n'
 if j<4:s+='  raw_reference_tail'+str(j+1)+'_550 '+' '.join((inputs if j+1<4 else[])+vals[:4*(j+1)])+'\n'
# Source tails preserve the four row constructions and the entire debug pass.
s+='''\ndef raw_native_tail4_550 (r0 r1 r2 r3 : Limbs64_550) : Result Limbs64_550 := do
  let rows := Array.make 4#usize [r0,r1,r2,r3] (by simp only [List.length_cons,List.length_nil]; rfl)
  let bound ← reference_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND
  let _ ← source_debug_matrix550 bound rows
'''
for j in range(4):s+=f'  let p{j} ← raw_pack{j}_550 r0 r1 r2 r3 bound\n'
s+='  .ok (Array.make 4#usize [p0,p1,p2,p3] (by simp only [List.length_cons,List.length_nil]; rfl))\n'
for j in range(3,-1,-1):
 s+=f'\ndef raw_native_tail{j}_550 (a b c d : Limbs32_550)'+(' ('+' '.join('r'+str(k)for k in range(j))+' : Limbs64_550)'if j else'')+' : Result Limbs64_550 := do\n'
 s+=f'  let r{j} ← raw_row550 a b c d {j}#usize\n'
 s+='  raw_native_tail'+str(j+1)+'_550 '+('a b c d 'if j+1<4 else'')+' '.join('r'+str(k)for k in range(j+1))+'\n'
s+='''\n/-- Pure delta refactoring of the exact emission, with every primitive opaque.
No recurrence, raw arithmetic or numerical cell is evaluated here. -/
theorem raw_reference_factor550 (input : Array aspis_core.field.QM31 4#usize) :
    reference_poseidon.external_local_packed_raw input = (do
'''+prefix+'  raw_reference_tail0_550 a a1 a2 a3) := by\n  rfl\n\n#print axioms raw_reference_factor550\nend PV_B3P_Association550227\n'
(L/'PV_B3P_RawTails550227.lean').write_text(s)
# Round-trip syntax check, including all reference input projections, constants,
# exact operations, proof arguments and the original dead debug reads.
roundtrip=prefix+''.join(chunks)
assert roundtrip==body
for j in range(4,-1,-1):
 prev='PV_B3P_RawTails550227'if j==4 else f'PV_B3P_RawTail{j+1}550227'
 code='import '+prev+'\n'+header+attrs
 arrays='(a4 a6 a7 a8 : Limbs32_550)'if j<4 else''
 params=(' ('+' '.join(vals[:4*j])+' : U64)')if j else''
 rows=['(Array.make 4#usize ['+','.join(vals[4*k:4*k+4])+'] (by simp only [List.length_cons,List.length_nil]; rfl))'for k in range(j)]
 source=f'raw_native_tail{j}_550 '+('a4 a6 a7 a8 'if j<4 else'')+' '.join(rows)
 ref=f'raw_reference_tail{j}_550 '+('a4 a6 a7 a8 'if j<4 else'')+' '.join(vals[:4*j])
 code+=f'\ntheorem raw_tail{j}_binding550 {arrays}{params} :\n    {source} =\n      {ref} := by\n'
 if j==4:
  code+='  unfold raw_native_tail4_550 raw_reference_tail4_550\n  simp only [ignored_source_debug_loops550]\n  exact (raw_suffix550 '+' '.join(vals)+').symm\n'
 else:
  code+=f'  unfold raw_native_tail{j}_550 raw_reference_tail{j}_550\n  rw [raw_row_continuation550]\n'
  code+='  simp only [four_index_zero550,four_index_one550,four_index_two550,four_index_three550,bind_tc_ok]\n'if j==0 else''
  code+=f'  simp only [raw_tail{j+1}_binding550]\n  rfl\n'
 code+=f'\n#print axioms raw_tail{j}_binding550\nend PV_B3P_Association550227\n'
 (L/f'PV_B3P_RawTail{j}550227.lean').write_text(code)
(R/'RAW-TAILS-GENERATOR-D550.json').write_text(json.dumps(dict(exact_reference_syntax_roundtrip=True,original_emission_sha256=hashlib.sha256(old.encode()).hexdigest(),fragments=len(chunks),source_is_reference=False,source='native tails use raw_row550, source_debug_matrix550 and raw_pack0..3_550',proof_shape='one row per bridge, no raised limits; reference factor is only exact syntax delta with primitives opaque'),indent=2)+'\n')
# Replace the failed whole-row-flattening bridge; keep the small prefix law.
p=L/'PV_B3P_RawSource550227.lean';s=p.read_text().replace('import PV_B3P_RawSuffix550227','import PV_B3P_RawTail0550227')
a=s.index('  let r0 ← raw_row550');b=s.index('\nattribute [local irreducible]',a)
s=s[:a]+'  raw_native_tail0_550 a b c d\n'+s[b:]
a=s.index('  unfold raw_source550\n',s.index('theorem raw_source_reference550'));b=s.index('\ntheorem raw_source_link550',a)
s=s[:a]+'''  rw [raw_reference_factor550]
  unfold raw_source550
  rw [raw_input_continuation550]
  simp only [four_index_zero550,four_index_one550,four_index_two550,four_index_three550,bind_tc_ok]
  simp only [raw_tail0_binding550]
  rfl
'''+s[b:]
p.write_text(s)
print('exact reference view, five one-row bridges, and source composition generated')
