import PV_B3P_CombinedAudit
import PV_B3P_WordLaw226V3
import PV_B3P_DigestRegions226V3
import PV_B3P_FrontierTotal226V3
import PV_B3P_EncodeSuccess226V3
import PV_B3P_Nonvacuity226V3
import PV_B3P_ReferenceOutcome226V3
import PV_B3P_Length226V3
import PV_B3P_EndianVerified226V3
import PV_B3P_LayoutCells226V3
namespace PV_B3P_FocusedClosure
open Aeneas Aeneas.Std ProverRwFull
set_option autoImplicit false
noncomputable section

-- A focused closure of the checked owned-reference installations, with all
-- native correspondence and privacy-endpoint obligations still explicit OPEN.
theorem reference_pair (base : ExternalTypes)
    (ops : @ExternalFuns (PV_B3P_CombinedAudit.Types base))
    (p : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
      (PV_B3P_CombinedAudit.Types base)) :
    (@ExternalFuns.op133 (PV_B3P_CombinedAudit.Types base)
      (PV_B3P_CombinedAudit.selected base ops) = .ok (.Ok PV_B3P_Install133.value)) ∧
    (@ExternalFuns.op226 (PV_B3P_CombinedAudit.Types base)
      (PV_B3P_CombinedAudit.selected base ops) p =
      PV_B3P_Install226V3.transport (PV_B3P_226V3.reference226.public_bytes
        (PV_B3P_PublicCarrier226V3.toSource base p))) :=
  ⟨PV_B3P_CombinedAudit.source133 base ops,PV_B3P_CombinedAudit.source226 base ops p⟩

#print axioms reference_pair
#print axioms PV_B3P_WordLaw226V3.complete_word
#print axioms PV_B3P_DigestRegions226V3.anchor_success
#print axioms PV_B3P_DigestRegions226V3.nullifier_success
#print axioms PV_B3P_FrontierTotal226V3.success
#print axioms PV_B3P_EncodeSuccess226V3.success
#print axioms PV_B3P_Nonvacuity226V3.installed_success
#print axioms PV_B3P_ReferenceOutcome226V3.no_outer_failure
#print axioms PV_B3P_Length226V3.installed_length
#print axioms PV_B3P_EndianVerified226V3.word_bytes
#print axioms PV_B3P_EndianVerified226V3.index_bytes
#print axioms PV_B3P_LayoutCells226V3.flat_cell
end
end PV_B3P_FocusedClosure
