import PV_B3P_LeadingStep12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false

def leading_tail12_7 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (state : LeadingState12) : Result (Array aspis_core.field.QM31 4#usize) := do
  let q21 ← Array.index_usize state 7#usize
  let q22 ← Array.index_usize openings.xor12_z 7#usize
  let q23 ← aspis_core.field.QM31.add q21 q22
  let state7 ← Array.update state 7#usize q23
  let state8 ← reference_poseidon.external_linear_lazy state7
  let a ← Array.index_usize reference_poseidon.EXTERNAL_INITIAL 0#usize
  let a1 ← reference_poseidon.full_round_m31_constants state8 a
  let a2 ← Array.index_usize reference_poseidon.EXTERNAL_INITIAL 1#usize
  reference_poseidon.full_round_m31_constants_packed a1 a2
attribute [local irreducible] aspis_core.field.QM31.add Array.index_usize Array.update leading_step12 leading_finish12
theorem leading_cell12_7 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (state : LeadingState12) :
    leading_tail12_7 openings state =
      (leading_step12 openings.xor12_z state 7#usize >>= leading_finish12) := by
  unfold leading_tail12_7
  conv_rhs => simp only [leading_step12,PV_B3P_Ordered227.bind_assoc]
  apply PV_B3P_Binding9227.bind_equal9
  intro v0
  apply PV_B3P_Binding9227.bind_equal9
  intro v1
  apply PV_B3P_Binding9227.bind_equal9
  intro v2
  apply PV_B3P_Binding9227.bind_equal9
  intro next
  unfold leading_finish12
  rfl
theorem leading_fold12_7 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (state : LeadingState12) :
    leading_tail12_7 openings state =
      (PV_B3P_Ordered227.fold (leading_step12 openings.xor12_z)
        [7#usize] state >>= leading_finish12) := by
  rw [leading_cell12_7]
  simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc]
  rfl
#print axioms leading_cell12_7
#print axioms leading_fold12_7
end PV_B3P_Binding12227
