import PV_B3P_ArrayInterface543227
import PV_B3P_NativeRoundQPlain15227
import PV_B3P_NativeRoundMPlain15227
import PV_B3P_NativeRoundMPacked15227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Association546227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Links13227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding13227 PV_B3P_Native15227
set_option autoImplicit false

/-- The source range threads the full state. Each lane performs the original
field calls and store, followed by exactly one external packed call. -/
def source_round_qpacked546 (state : RoundState10)
    (constants1 : Array aspis_core.field.QM31 16#usize) :
    Result (Array aspis_core.field.QM31 4#usize) := do
  let state1 ← range_loop13 (round_q_step10 constants1) 0#usize 16#usize state
  reference_poseidon.external_linear_packed state1

theorem round_qpacked_reference546 (state : RoundState10)
    (constants1 : Array aspis_core.field.QM31 16#usize) :
    source_round_qpacked546 state constants1 = reference_poseidon.full_round_packed state constants1 := by
  unfold source_round_qpacked546
  rw [range_sixteen13]
  exact (full_round_packed_source_fold11 state constants1).symm

theorem round_qplain_source_link546 :
    PV_B3P_Link_poseidon_full_round native_round_QPlain15 :=
  funext fun state => funext fun constants1 => native_round_QPlain_binding15 state constants1

theorem round_mplain_source_link546 :
    PV_B3P_Link_poseidon_full_round_m31_constants native_round_MPlain15 :=
  funext fun state => funext fun constants1 => native_round_MPlain_binding15 state constants1

theorem round_qpacked_source_link546 :
    PV_B3P_Link_poseidon_full_round_packed source_round_qpacked546 :=
  funext fun state => funext fun constants1 => round_qpacked_reference546 state constants1

theorem round_mpacked_source_link546 :
    PV_B3P_Link_poseidon_full_round_m31_constants_packed native_round_MPacked15 :=
  funext fun state => funext fun constants1 => native_round_MPacked_binding15 state constants1

#print axioms round_qpacked_reference546
#print axioms round_qplain_source_link546
#print axioms round_mplain_source_link546
#print axioms round_qpacked_source_link546
#print axioms round_mpacked_source_link546
end PV_B3P_Association546227
