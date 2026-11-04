import NFP_DotCaller
import NFG_QueryLoopSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_LoopTransport
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody NFP_QueryCuts NFP_DotInstall NFG_QueryLoopDefs
/-- Pointwise child equality includes every error and machine Result branch.
It is derived by installing the CLOSED NFM dot packet, not assumed. -/
theorem child (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array E 29#usize) (qPlace gPlace : Nat)
 (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g))
 (geometry : verifier.QueryGeometry) :
 (fun a b => verifier.candidate.query_values (oracle ops qPlace gPlace) proof p a g none geometry b) =
 (fun a b => verifier.candidate.query_values (cohort ops) proof p a g none geometry b) := by
 funext a b
 exact NFP_DotCaller.query ops proof p a g qPlace gPlace canonical geometry b

/-- Existing finite partial-Result induction transfers the SAME state, not
an independently successful second execution. -/
theorem complete (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array E 29#usize) (qPlace gPlace : Nat)
 (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g))
 (geometry : verifier.QueryGeometry) (finish : Usize) (fuel : Nat) (state : State)
 (budget : Budget finish fuel state) :
 verifier.candidate.query_loop_loop (oracle ops qPlace gPlace) state proof p g none geometry finish =
 verifier.candidate.query_loop_loop (cohort ops) state proof p g none geometry finish := by
 rw [←NFG_QueryLoopSource.complete _ _ _ _ _ _ fuel state budget,
  ←NFG_QueryLoopSource.complete _ _ _ _ _ _ fuel state budget]
 rw [child ops proof p g qPlace gPlace canonical geometry]
#print axioms child
#print axioms complete
end AspisR1.NFP_LoopTransport
end
