import PV_B3P_Operations12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding11227 PV_B3P_Binding10227 Result
set_option autoImplicit false
def source_round_m_plain12 (state : RoundState10) (constants1 : Array U32 16#usize) : Result (Array aspis_core.field.QM31 16#usize) :=
  PV_B3P_Ordered227.fold (round_m_step10 constants1) [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize] state >>= reference_poseidon.external_linear_lazy
def source_round_m_packed12 (state : RoundState10) (constants1 : Array U32 16#usize) : Result (Array aspis_core.field.QM31 4#usize) :=
  PV_B3P_Ordered227.fold (round_m_step10 constants1) [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize] state >>= reference_poseidon.external_linear_packed
def source_leading_finish12 (state : LeadingState12) : Result (Array aspis_core.field.QM31 4#usize) := do
  let state ← reference_poseidon.external_linear_lazy state
  let even ← Array.index_usize reference_poseidon.EXTERNAL_INITIAL 0#usize
  let state ← source_round_m_plain12 state even
  let odd ← Array.index_usize reference_poseidon.EXTERNAL_INITIAL 1#usize
  source_round_m_packed12 state odd

attribute [local irreducible] Array.index_usize reference_poseidon.external_linear_lazy

theorem leading_finish_rounds12 (state : LeadingState12) :
    leading_finish12 state = source_leading_finish12 state := by
  unfold leading_finish12 source_leading_finish12
  simp only [full_round_m31_constants_source_fold11,full_round_m31_constants_packed_source_fold11,
    source_round_m_plain12,source_round_m_packed12]

def source_leading_rounds12 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) : Result (Array aspis_core.field.QM31 4#usize) :=
  PV_B3P_Ordered227.fold (leading_step12 openings.xor12_z)
    [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize] openings.z >>= source_leading_finish12

theorem leading_rounds_binding12 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
    reference_poseidon.leading_pair_packed openings = source_leading_rounds12 openings := by
  rw [leading_pair_packed_binding12]
  unfold source_leading_rounds12
  exact congrArg (fun finish => PV_B3P_Ordered227.fold (leading_step12 openings.xor12_z)
    [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize] openings.z >>= finish)
    (funext leading_finish_rounds12)
#print axioms leading_finish_rounds12
#print axioms leading_rounds_binding12
end PV_B3P_Binding12227
