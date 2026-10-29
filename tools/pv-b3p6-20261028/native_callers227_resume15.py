from pathlib import Path
L=Path('evidence/pv-b3p6-20261028/lean');h='''namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 PV_B3P_Success227 Result
set_option autoImplicit false
'''
s='import PV_B3P_DigestLoopBridge11227\nimport PV_B3P_RangeFold13227\n'+h+'''
def native_public_digest15 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result Digest8Q := do
  let d0 ← digest_stage_00 public1 openings selectors
  let d1 ← digest_stage_01 public1 openings selectors d0
  let d2 ← digest_stage_02 public1 openings selectors d1
  let d3 ← digest_stage_03 public1 openings selectors d2
  let next ← range_loop13 (digest_level11 public1 openings selectors) 0#usize 20#usize d3
  digest_stage_24 public1 openings selectors next

theorem native_public_digest_binding15 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    native_public_digest15 public1 openings selectors = reference_terminal.public_digest_lanes public1 openings selectors := by
  rw [public_digest_source_loop_binding11]
  unfold native_public_digest15 public_digest_source_loop11
  simp only [range_loop_binding13]
#print axioms native_public_digest_binding15
end PV_B3P_Native15227
''';(L/'PV_B3P_NativePublicDigest15227.lean').write_text(s)
s='import PV_B3P_SumHighLink13227\nimport PV_B3P_TransitionLoan14227\n'+h+'''
open PV_B3P_Loans14227
/-- Slice order and the complete ordered list of range endpoints are retained.
Every source range is cloned by value; neither shared loan is changed. -/
def native_sum_high15 (selectors : Shared14 reference_copy_terminal.Selectors)
    (ranges : Shared14 (List (Usize × Usize))) : Result aspis_core.field.QM31 :=
  source_sum_ranges13 selectors.value.high ranges.value aspis_core.field.QM31.ZERO

theorem native_sum_high_binding15 (selectors : Shared14 reference_copy_terminal.Selectors)
    (ranges : Shared14 (List (Usize × Usize))) :
    native_sum_high15 selectors ranges =
      PV_B3P_Links13227.sum_ranges_reference13 selectors.value.high ranges.value aspis_core.field.QM31.ZERO :=
  sum_ranges_binding13 selectors.value.high ranges.value aspis_core.field.QM31.ZERO
#print axioms native_sum_high_binding15
end PV_B3P_Native15227
''';(L/'PV_B3P_NativeSumHigh15227.lean').write_text(s)
s='import PV_B3P_NativeLeading15227\nimport PV_B3P_ProjectedLink13227\n'+h+'''
def native_projected15 := projected_prefix13 native_leading15

theorem native_projected_binding15
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors) :
    native_projected15 openings selectors = reference_poseidon.evaluate_state_only_poseidon_oracle_projected openings selectors := by
  have leading : native_leading15 = reference_poseidon.leading_pair_packed := funext native_leading_binding15
  unfold native_projected15
  rw [leading]
  exact (projected_staging13 openings selectors).symm
#print axioms native_projected_binding15
end PV_B3P_Native15227
''';(L/'PV_B3P_NativeProjected15227.lean').write_text(s)
