import R1Z.PV_RDB2C_PV_B2_F_AllocationEffects
import R1Z.PV_RDB2C_PV_B2_F_MaterializeFrozen
set_option autoImplicit false
namespace PV_B2_F_MaterializeRequest
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_MutationStep
abbrev Outcome := PV_B2_F_AllocationTransport.Outcome
/-- Frozen source order: pure total powers before the single allocation request,
then ordered mutable iteration; every request failure/divergence is preserved. -/
def original (request : Result Outcome) (w : host_weights.Weights) (kappa : E) :
    Result PV_B2_F_AllocationTransport.RustResult := do
  let k ← host_weights.powers7 kappa
  let event ← request
  match event with
  | .denied => ok (.Err verifier.Error.Allocation)
  | .supplied => do
    let out ← PV_B2_F_MaterializeFrozen.remaining w k 1024 0#usize PV_B2_F_AllocationTransport.zeros
    ok (.Ok out)

theorem after_eq_before (request : Result Outcome) (w : host_weights.Weights) (kappa : E) :
    (request >>= fun event => PV_B2_F_MaterializeFrozen.original event w kappa) =
      original request w kappa := by
  obtain ⟨k,hk⟩ := PV_B2_C_Powers7Total.source kappa
  unfold original
  simp only [hk,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro event _
  cases event <;> simp only [PV_B2_F_MaterializeFrozen.original,hk,bind_tc_ok]

theorem complete_result (request : Result Outcome) (w : host_weights.Weights) (kappa : E) :
    PV_B2_F_AllocationEffects.copied request w kappa = original request w kappa := by
  rw [PV_B2_F_AllocationEffects.complete_result]
  trans (request >>= fun event => PV_B2_F_MaterializeFrozen.original event w kappa)
  · unfold PV_B2_F_AllocationEffects.original
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro event _
    exact PV_B2_F_MaterializeFrozen.originals event w kappa
  · exact after_eq_before request w kappa
#print axioms after_eq_before
#print axioms complete_result
end PV_B2_F_MaterializeRequest
