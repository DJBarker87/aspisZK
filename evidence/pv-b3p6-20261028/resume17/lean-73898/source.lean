import PV_B3P_DirectLinks540227
import PV_B3P_PreweightedTotal540227
import PV_B3P_DirectMaskBridge17227
namespace PV_B3P_Direct540227
open PV_B3P_227 PV_B3P_Links13227
set_option autoImplicit false

/-- Joint satisfaction for the three direct extraction definitions. All three
are total equations. This does not instantiate any other changed-body slot,
source-closure law, endpoint premise, or unresolved mask external. -/
theorem direct_total_links540 :
    PV_B3P_Link_terminal_absorption_lanes_literal host_terminal.absorption_lanes_literal ∧
    PV_B3P_Link_terminal_add_digest_binding host_terminal.add_digest_binding ∧
    PV_B3P_Link_terminal_add_preweighted (@host_terminal.add_preweighted) :=
  ⟨extracted_absorption_link540,extracted_digest_link540,extracted_preweighted_total_link540⟩

#print axioms direct_total_links540
#print axioms inclusive_std_while540
#print axioms preweighted_extraction_total540
#print axioms preweighted_actual_continuation540
#print axioms PV_B3P_Direct17227.mask_extraction_reference_on_domain17
end PV_B3P_Direct540227
