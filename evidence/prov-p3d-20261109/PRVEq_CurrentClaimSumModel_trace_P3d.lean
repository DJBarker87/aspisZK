-- PCVD_ item 2 (instance boundary): fresh `trace::value` (PCQF_E006 text) has parameter type
-- `aspis_core.field.wide_exact.WideExact`, an opaque external type in the cross-crate emission.  The gate declares its own
-- structure `aspis_core.field.WideExact`.  The fresh body ignores `x`, so it is parametric in that type: we state it with the external
-- type as a type parameter W and instantiate W with the gate structure.  The identification of the external type with the gate
-- structure is NOT proved here (type-level hand model, P6).
import Aeneas
import CurrentClaimSumModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1CurrentPreparedClaim
namespace PRVFresh_CurrentClaimSumModel_ns_AspisR1CurrentPreparedClaim_1

/-- [aspis_r1_cost_probe::trace::value]  (fresh text; external type WideExact abstracted as W)
    Source: 'crates/aspis-r1-cost-probe/src/trace.rs', lines 6:0-11:1 -/
def trace.value {W : Type}
  (tag : Std.U16) (index : Std.Usize)
  (x : W) :
  Result Unit
  := do
  ok ()

end PRVFresh_CurrentClaimSumModel_ns_AspisR1CurrentPreparedClaim_1
end AspisR1CurrentPreparedClaim

set_option maxHeartbeats 200000 in
theorem PRVD.Eq.trace.value :
    @AspisR1CurrentPreparedClaim.PRVFresh_CurrentClaimSumModel_ns_AspisR1CurrentPreparedClaim_1.trace.value AspisR1CurrentPreparedClaim.aspis_core.field.WideExact
      = @AspisR1CurrentPreparedClaim.trace.value := by
  delta AspisR1CurrentPreparedClaim.PRVFresh_CurrentClaimSumModel_ns_AspisR1CurrentPreparedClaim_1.trace.value AspisR1CurrentPreparedClaim.trace.value
  rfl
#print axioms PRVD.Eq.trace.value
