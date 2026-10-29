"""Compose the original digest entry one head/branch continuation at a time."""
from pathlib import Path
import sys
L=Path('evidence/pv-b3p6-20261028/lean')
params='''(public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)'''
s='''import PV_B3P_DigestReadSuffix900227
import PV_B3P_LiftHeadEq9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Success227
set_option autoImplicit false
attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry
'''
s+=f'''\ntheorem digest_source_factor9 {params} :
    reference_terminal.public_digest_lanes public1 openings selectors =
      digest_suffix_00 public1 openings selectors := by
  unfold reference_terminal.public_digest_lanes
'''
for i in range(24):
 if i==2:s+='  conv_rhs => rw [digest_suffix_02_equation,recipient_stage_action9]\n'
 else:s+=f'  conv_rhs => rw [digest_suffix_{i:02}_equation]; simp only [digest_stage_{i:02},digest_assoc,lift,bind_tc_ok]\n'
 if i in [0,1,3]:
  block={0:56,1:26,3:32}[i]
  s+=f'  apply lift_head_equal9 (Usize.wrapping_mul {block}#usize 16#usize)\n  apply lift_head_equal9 (Usize.wrapping_add (Usize.wrapping_mul {block}#usize 16#usize) 11#usize)\n'
  for j in range(2):s+=f'  apply bind_equal9\n  intro head_{i}_{j}\n'
 elif i==2:s+='  apply recipient_equal9 public1.recipient head_1_1 openings.z selectors\n  intro recipient_output\n  apply equal_ok_head9 recipient_output\n'
 else:
  output='head_3_1'if i==4 else f'frontier_output_{i-1}'
  block=f'(Usize.wrapping_add 34#usize {i-4}#usize)'
  bit=f'((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index {i-4}#u32) &&& 1#u64)'
  if i==4:s+=f'  apply lift_head_equal9 {block}\n'
  s+=f'  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index {i-4}#u32)\n  apply lift_head_equal9 {bit}\n'
  s+=f'  conv_rhs => change (frontier_primitive9 {output} openings.z selectors public1.transition.live_snapshot.frontier {i-4}#usize {block} {bit} >>= digest_suffix_{i+1:02} public1 openings selectors); rw [frontier_primitive_bind9]\n'
  s+=f'  apply frontier_equal9 {output} openings.z selectors public1.transition.live_snapshot.frontier {i-4}#usize {block} {bit}\n  intro frontier_output_{i}\n  apply equal_ok_head9 frontier_output_{i}\n'
s+='  rfl\n\n#print axioms digest_source_factor9\n'
s+=f'''\ntheorem public_digest_read_binding9 {params} :
    reference_terminal.public_digest_lanes public1 openings selectors =
      digest_direct_suffix9_00 public1 openings selectors :=
  (digest_source_factor9 public1 openings selectors).trans
    (digest_suffix_read_binding9_00 public1 openings selectors)
#print axioms public_digest_read_binding9
end PV_B3P_Binding9227
'''
p=L/'PV_B3P_DigestReadBridge9227.lean'
if '--check'in sys.argv:assert p.read_text()==s
else:p.write_text(s)
