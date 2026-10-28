import R1Z.PV_RDB2C_PV_B2_F_AllocationTransport
set_option autoImplicit false
namespace PV_B2_F_AllocationEffects
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_MutationStep
abbrev Outcome := PV_B2_F_AllocationTransport.Outcome
abbrev RustResult := PV_B2_F_AllocationTransport.RustResult
/-- Universal request-result context: fail/div are retained, and a returned
allocation outcome covers both Rust success and Allocation error. -/
def copied (request : Result Outcome) (w : host_weights.Weights) (kappa : E) : Result RustResult :=
  request >>= fun event => PV_B2_F_AllocationTransport.copied event w kappa

def original (request : Result Outcome) (w : host_weights.Weights) (kappa : E) : Result RustResult :=
  request >>= fun event => PV_B2_F_AllocationTransport.original event w kappa

theorem complete_result (request : Result Outcome) (w : host_weights.Weights) (kappa : E) :
    copied request w kappa = original request w kappa := by
  unfold copied original
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro event _
  exact PV_B2_F_AllocationTransport.equal event w kappa

theorem failure (w : host_weights.Weights) (kappa : E) (e : Error) :
    copied (fail e) w kappa = fail e := by simp only [copied,bind_tc_fail]
theorem divergence (w : host_weights.Weights) (kappa : E) :
    copied div w kappa = div := by simp only [copied,bind_tc_div]
theorem denied (w : host_weights.Weights) (kappa : E) :
    copied (ok .denied) w kappa = ok (.Err verifier.Error.Allocation) := rfl

theorem supplied (w : host_weights.Weights) (kappa : E) :
    ∃ out, copied (ok .supplied) w kappa = ok (.Ok out) :=
  PV_B2_F_AllocationTransport.supplied w kappa
#print axioms complete_result
#print axioms failure
#print axioms divergence
#print axioms denied
#print axioms supplied
end PV_B2_F_AllocationEffects
