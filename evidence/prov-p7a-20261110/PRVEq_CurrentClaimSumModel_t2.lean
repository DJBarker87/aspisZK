-- PCWT_ binding discharge for AspisR1CurrentPreparedClaim.trace.value (module CurrentClaimSumModel), route (b).
-- What was bound: the fresh trace::value text (PCQF_E006, frozen 4bb3b3f, crates/aspis-r1-cost-probe/src/trace.rs 6:0-11:1) takes its argument at the
-- external type aspis_core::field::wide_exact::WideExact; P3d stated it for an abstract W and instantiated W at the gate structure
-- aspis_core.field.WideExact without proving the identification.  Here W is the FRESH frozen WideExact structure (PCWL_L014 emission, no external)
-- and the identification with the gate structure is the proved type equivalence PRVEq.CurrentClaimSumModel_w3...WideExact.equiv.
import Aeneas
import CurrentClaimSumModel
import PRVEq_CurrentClaimSumModel_trace_P3d
import PRVEq_CurrentClaimSumModel_w3
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

set_option maxHeartbeats 200000 in
theorem PRVEq.CurrentClaimSumModel_t2.trace.value_frozen_wide
    (tag : Std.U16) (index : Std.Usize)
    (x : AspisR1CurrentPreparedClaim.PRVFresh_CurrentClaimSumModel_w3.aspis_core.field.wide_exact.WideExact) :
    @AspisR1CurrentPreparedClaim.PRVFresh_CurrentClaimSumModel_ns_AspisR1CurrentPreparedClaim_1.trace.value
      AspisR1CurrentPreparedClaim.PRVFresh_CurrentClaimSumModel_w3.aspis_core.field.wide_exact.WideExact tag index x =
    AspisR1CurrentPreparedClaim.trace.value tag index
      (PRVEq.CurrentClaimSumModel_w3.aspis_core.field.wide_exact.WideExact.equiv x) := by
  delta AspisR1CurrentPreparedClaim.PRVFresh_CurrentClaimSumModel_ns_AspisR1CurrentPreparedClaim_1.trace.value AspisR1CurrentPreparedClaim.trace.value
  rfl
#print axioms PRVEq.CurrentClaimSumModel_t2.trace.value_frozen_wide
