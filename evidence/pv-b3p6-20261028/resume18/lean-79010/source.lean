import PV_B3P_RoundSource546227
import PV_B3P_NativeLeading15227
namespace PV_B3P_Association546227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Links13227 PV_B3P_Binding10227 PV_B3P_Binding12227 PV_B3P_Binding13227 PV_B3P_Native15227
set_option autoImplicit false

/-- Both leading rounds consume the restored full state of the preceding call. -/
def source_leading_finish546 (state : LeadingState12) :
    Result (Array aspis_core.field.QM31 4#usize) := do
  let state1 ← reference_poseidon.external_linear_lazy state
  let even ← Array.index_usize reference_poseidon.EXTERNAL_INITIAL 0#usize
  let state2 ← native_round_MPlain15 state1 even
  let odd ← Array.index_usize reference_poseidon.EXTERNAL_INITIAL 1#usize
  native_round_MPacked15 state2 odd

attribute [local irreducible] reference_poseidon.external_linear_lazy Array.index_usize

theorem leading_finish_reference546 (state : LeadingState12) :
    source_leading_finish546 state = leading_finish12 state := by
  unfold source_leading_finish546 leading_finish12
  simp only [native_round_MPlain_binding15,native_round_MPacked_binding15]

def source_leading546 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
    Result (Array aspis_core.field.QM31 4#usize) := do
  let state ← range_loop13 (leading_step12 openings.xor12_z) 0#usize 8#usize openings.z
  source_leading_finish546 state

theorem leading_source_reference546
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
    source_leading546 openings = reference_poseidon.leading_pair_packed openings := by
  rw [← native_leading_binding15]
  unfold source_leading546 native_leading15
  simp only [leading_finish_reference546]

theorem leading_source_link546 : PV_B3P_Link_poseidon_leading_pair_packed source_leading546 :=
  funext leading_source_reference546

#print axioms leading_finish_reference546
#print axioms leading_source_reference546
#print axioms leading_source_link546
end PV_B3P_Association546227
