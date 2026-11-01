import PV_B3P_RoundSource546227
import PV_B3P_LeadingSource546227
import PV_B3P_CopySource546227
import PV_B3P_ScheduleSource546227
namespace PV_B3P_Association546227
open PV_B3P_Links13227 PV_B3P_Native15227
set_option autoImplicit false

/-- Focused local links only; source maps, optimized dispatch and the actual
callback/source-cone obligations are separately recorded evidence. -/
theorem local_source_links546 :
    PV_B3P_Link_poseidon_full_round native_round_QPlain15 ∧
    PV_B3P_Link_poseidon_full_round_m31_constants native_round_MPlain15 ∧
    PV_B3P_Link_poseidon_full_round_packed source_round_qpacked546 ∧
    PV_B3P_Link_poseidon_full_round_m31_constants_packed native_round_MPacked15 ∧
    PV_B3P_Link_poseidon_leading_pair_packed source_leading546 ∧
    PV_B3P_Link_copy_active_literal native_active15 ∧
    PV_B3P_Link_copy_pattern_values_literal native_pattern15 ∧
    PV_B3P_Link_terminal_add_schedule_lanes native_schedule15 :=
  ⟨round_qplain_source_link546,round_mplain_source_link546,
   round_qpacked_source_link546,round_mpacked_source_link546,
   leading_source_link546,active_literal_source_link546,
   pattern_literal_source_link546,schedule_source_link546⟩

#print axioms round_qpacked_reference546
#print axioms round_qplain_source_link546
#print axioms round_mplain_source_link546
#print axioms round_qpacked_source_link546
#print axioms round_mpacked_source_link546
#print axioms leading_finish_reference546
#print axioms leading_source_reference546
#print axioms leading_source_link546
#print axioms active_literal_source_link546
#print axioms pattern_literal_source_link546
#print axioms schedule_source_link546
#print axioms local_source_links546
end PV_B3P_Association546227
