import PV_B3P_DirectAudit540227
import PV_B3P_MaskBridge542227
import PV_B3P_MaskIntrinsicSpec542227
import PV_B3P_NativeSumHigh15227
namespace PV_B3P_Audit542227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Direct540227 PV_B3P_Links13227
open PV_B3P_MaskSource542227 PV_B3P_Correct14227 PV_B3P_Direct17227
set_option autoImplicit false

/-- Changed direct import closure plus the original total sum model Link.
Source association for sum is the separately checked own-1 dossier, not an
interpretation inferred from this conjunction. Intrinsic implementations
remain V370. No other source model slot or callback premise is supplied. -/
theorem changed_local_links542 :
    PV_B3P_Link_terminal_absorption_lanes_literal host_terminal.absorption_lanes_literal ∧
    PV_B3P_Link_terminal_add_digest_binding host_terminal.add_digest_binding ∧
    PV_B3P_Link_terminal_add_preweighted (@host_terminal.add_preweighted) ∧
    (∀ (values : Array aspis_core.field.QM31 16#usize) (mask : U16),
      MaskAllowed mask → mask_source542 values mask =
        reference_copy_terminal.selector_mask_sum_16 values mask) ∧
    PV_B3P_Link_terminal_sum_high PV_B3P_Binding13227.source_sum_high13 :=
  ⟨extracted_absorption_link540,extracted_digest_link540,
    extracted_preweighted_total_link540,mask_source_reference542,
    PV_B3P_Binding13227.sum_high_link13⟩

#print axioms changed_local_links542
#print axioms ctpop16_nat542
#print axioms cttz16_first_set542
#print axioms mask_integer_source_laws542
#print axioms mask_external_boundary542
#print axioms PV_B3P_Native15227.native_sum_high_binding15
end PV_B3P_Audit542227
