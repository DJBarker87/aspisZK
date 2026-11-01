import PV_B3P_RoundSource546227
import PV_B3P_LeadingSource546227
import PV_B3P_CopySource546227
import PV_B3P_ScheduleSource546227
import PV_B3P_DigestSource547227
import PV_B3P_PathSource547227
import PV_B3P_PackedExternal547227
namespace PV_B3P_Association547227
open PV_B3P_Links13227 PV_B3P_Native15227 PV_B3P_Association546227
set_option autoImplicit false

/-- Actual fixed local interpreters only; source dossiers and whole callback
closure remain separate. This theorem introduces no link hypotheses. -/
theorem local_source_links547 :
    PV_B3P_Link_poseidon_full_round native_round_QPlain15 ∧
    PV_B3P_Link_poseidon_full_round_m31_constants native_round_MPlain15 ∧
    PV_B3P_Link_poseidon_full_round_packed source_round_qpacked546 ∧
    PV_B3P_Link_poseidon_full_round_m31_constants_packed native_round_MPacked15 ∧
    PV_B3P_Link_poseidon_leading_pair_packed source_leading546 ∧
    PV_B3P_Link_copy_active_literal native_active15 ∧
    PV_B3P_Link_copy_pattern_values_literal native_pattern15 ∧
    PV_B3P_Link_terminal_add_schedule_lanes native_schedule15 ∧
    PV_B3P_Link_terminal_public_digest_lanes native_public_digest15 ∧
    PV_B3P_Link_terminal_path_lanes_literal native_path15 ∧
    PV_B3P_Link_poseidon_external_linear_packed source_external_packed547 :=
  ⟨round_qplain_source_link546,round_mplain_source_link546,
   round_qpacked_source_link546,round_mpacked_source_link546,
   leading_source_link546,active_literal_source_link546,
   pattern_literal_source_link546,schedule_source_link546,
   public_digest_source_link547,path_literal_source_link547,
   external_packed_source_link547⟩

#print axioms round_qplain_source_link546
#print axioms round_mplain_source_link546
#print axioms round_qpacked_source_link546
#print axioms round_mpacked_source_link546
#print axioms leading_source_link546
#print axioms active_literal_source_link546
#print axioms pattern_literal_source_link546
#print axioms schedule_source_link546
#print axioms public_digest_source_link547
#print axioms path_literal_source_link547
#print axioms external_packed_source_link547
#print axioms local_source_links547
end PV_B3P_Association547227
