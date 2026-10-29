"""Compose the20 named digest levels without expanding any field operation."""
from pathlib import Path
import sys
L=Path('evidence/pv-b3p6-20261028/lean');h='namespace PV_B3P_Binding11227\nopen Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Success227\nset_option autoImplicit false\n'
params='''(public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)'''
s=''.join(f'import PV_B3P_DigestLevel11{i:02}227\n'for i in range(20))+'import PV_B3P_DigestReadBridge9227\nimport PV_B3P_Indices2011227\n'+h
s+='attribute [local irreducible] digest_level11 digest_stage_24 reference_terminal.public_digest_lanes\n'
s+=f'''theorem digest_suffix_loop11 {params} (output : Digest8Q) :
    digest_direct_suffix9_04 public1 openings selectors output = (do
      let next ← loop (usize_body (digest_level11 public1 openings selectors) 20#usize) (output,0#usize)
      digest_stage_24 public1 openings selectors next) := by
  rw [loop_as_fold11 (digest_level11 public1 openings selectors) 20#usize 0#usize 20 output (Eq.refl _),indices11_20]
  conv_rhs => simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  unfold digest_direct_suffix9_04
  rw [digest_level_binding11_00]
  apply bind_equal9
  intro d0
  unfold digest_direct_suffix9_05
  rw [digest_level_binding11_01]
  apply bind_equal9
  intro d1
  unfold digest_direct_suffix9_06
  rw [digest_level_binding11_02]
  apply bind_equal9
  intro d2
  unfold digest_direct_suffix9_07
  rw [digest_level_binding11_03]
  apply bind_equal9
  intro d3
  unfold digest_direct_suffix9_08
  rw [digest_level_binding11_04]
  apply bind_equal9
  intro d4
  unfold digest_direct_suffix9_09
  rw [digest_level_binding11_05]
  apply bind_equal9
  intro d5
  unfold digest_direct_suffix9_10
  rw [digest_level_binding11_06]
  apply bind_equal9
  intro d6
  unfold digest_direct_suffix9_11
  rw [digest_level_binding11_07]
  apply bind_equal9
  intro d7
  unfold digest_direct_suffix9_12
  rw [digest_level_binding11_08]
  apply bind_equal9
  intro d8
  unfold digest_direct_suffix9_13
  rw [digest_level_binding11_09]
  apply bind_equal9
  intro d9
  unfold digest_direct_suffix9_14
  rw [digest_level_binding11_10]
  apply bind_equal9
  intro d10
  unfold digest_direct_suffix9_15
  rw [digest_level_binding11_11]
  apply bind_equal9
  intro d11
  unfold digest_direct_suffix9_16
  rw [digest_level_binding11_12]
  apply bind_equal9
  intro d12
  unfold digest_direct_suffix9_17
  rw [digest_level_binding11_13]
  apply bind_equal9
  intro d13
  unfold digest_direct_suffix9_18
  rw [digest_level_binding11_14]
  apply bind_equal9
  intro d14
  unfold digest_direct_suffix9_19
  rw [digest_level_binding11_15]
  apply bind_equal9
  intro d15
  unfold digest_direct_suffix9_20
  rw [digest_level_binding11_16]
  apply bind_equal9
  intro d16
  unfold digest_direct_suffix9_21
  rw [digest_level_binding11_17]
  apply bind_equal9
  intro d17
  unfold digest_direct_suffix9_22
  rw [digest_level_binding11_18]
  apply bind_equal9
  intro d18
  unfold digest_direct_suffix9_23
  rw [digest_level_binding11_19]
  apply bind_equal9
  intro d19
  unfold digest_direct_suffix9_24
  exact Eq.refl _
#print axioms digest_suffix_loop11
'''
s+=f'def public_digest_source_loop11 {params} : Result Digest8Q := do\n  let d0 ← digest_stage_00 public1 openings selectors\n  let d1 ← digest_stage_01 public1 openings selectors d0\n  let d2 ← digest_stage_02 public1 openings selectors d1\n  let d3 ← digest_stage_03 public1 openings selectors d2\n  let next ← loop (usize_body (digest_level11 public1 openings selectors) 20#usize) (d3,0#usize)\n  digest_stage_24 public1 openings selectors next\n'
s+=f'''theorem public_digest_source_loop_binding11 {params} :
    reference_terminal.public_digest_lanes public1 openings selectors = public_digest_source_loop11 public1 openings selectors := by
  rw [public_digest_read_binding9]
  unfold digest_direct_suffix9_00 digest_direct_suffix9_01 digest_direct_suffix9_02 digest_direct_suffix9_03 public_digest_source_loop11
  apply bind_equal9
  intro d0
  apply bind_equal9
  intro d1
  apply bind_equal9
  intro d2
  apply bind_equal9
  intro d3
  exact digest_suffix_loop11 public1 openings selectors d3
#print axioms public_digest_source_loop_binding11
end PV_B3P_Binding11227
'''
p=L/'PV_B3P_DigestLoopBridge11227.lean'
if '--check'in sys.argv:assert p.read_text()==s
else:p.write_text(s)
