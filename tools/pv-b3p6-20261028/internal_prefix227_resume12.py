"""The uniform fifteen-term prefix is linear and has no arithmetic reduction.
Factor it once, then compose with the already isolated lane-write cells.
"""
from pathlib import Path
import re,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean'
raw=(D/'raw227-composition-resume5/Funs.lean').read_text()
decl=re.search(r'^def reference_poseidon.internal_linear_lazy\s*\n[\s\S]*?(?=^/--|\Z)',raw,re.M)[0]
lines=decl.split(':= do\n',1)[1].strip('\n').splitlines()
a=next(i for i,l in enumerate(lines) if 'let q1 ← Array.index_usize state' in l)
b=next(i for i,l in enumerate(lines) if 'let full_sum ←'in l)
steps='\n'.join(lines[a:b])+'\n  .ok part_sum15\n'
idx=', '.join(f'{i}#usize'for i in range(1,16))
h='namespace PV_B3P_Binding12227\nopen Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result\nset_option autoImplicit false\n'
s='import PV_B3P_InternalFinish12227\n'+h
s+='def internal_sum_sequence12 (state : InternalState12) (part_sum : InternalSum12) : Result InternalSum12 := do\n'+steps
s+='attribute [local irreducible] Array.index_usize Array.update reference_poseidon.internal_sum227 reference_poseidon.extension_limbs reference_poseidon.internal_full_sum227 reference_poseidon.internal_zero227 reference_poseidon.internal_shift227\n'
s+=f'''theorem internal_sum_sequence_fold12 (state : InternalState12) (part_sum : InternalSum12) :
    internal_sum_sequence12 state part_sum =
      PV_B3P_Ordered227.fold (internal_sum_step12 state) [{idx}] part_sum := by
  simp only [internal_sum_sequence12,PV_B3P_Ordered227.fold,internal_sum_step12,
    PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

def internal_entry_prefix12 (state : InternalState12) : Result InternalState12 := do
  let first ← Array.index_usize state 0#usize
  let old_zero ← reference_poseidon.extension_limbs first
  let part_sum ← internal_sum_sequence12 state (Array.repeat 4#usize 0#u64)
  internal_finish12 state old_zero part_sum

theorem internal_entry_factor12 (state : InternalState12) :
    reference_poseidon.internal_linear_lazy state = internal_entry_prefix12 state := by
  unfold reference_poseidon.internal_linear_lazy internal_entry_prefix12 internal_sum_sequence12
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
'''
for i in range(32):s+=f'  apply bind_equal9\n  intro value_{i}\n'
s+='  unfold internal_finish12 internal_output_tail12_01\n  rfl\n'
s+='#print axioms internal_sum_sequence_fold12\n#print axioms internal_entry_factor12\nend PV_B3P_Binding12227\n'
p=L/'PV_B3P_InternalPrefix12227.lean'
if '--check'in sys.argv:assert p.read_text()==s
else:p.write_text(s)
p=L/'PV_B3P_InternalBinding12227.lean';s=p.read_text();s=s.replace('import PV_B3P_InternalSum1201227','import PV_B3P_InternalPrefix12227')
a=s.index('theorem internal_linear_binding12')
s=s[:a]+'''theorem internal_linear_binding12 (state : InternalState12) :
    reference_poseidon.internal_linear_lazy state = source_internal12 state := by
  rw [internal_entry_factor12]
  unfold internal_entry_prefix12 source_internal12
  simp only [internal_sum_sequence_fold12]

#print axioms internal_linear_binding12
end PV_B3P_Binding12227
'''
if '--check'in sys.argv:assert p.read_text()==s
else:p.write_text(s)
