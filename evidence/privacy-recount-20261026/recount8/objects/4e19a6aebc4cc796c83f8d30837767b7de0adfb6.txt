import R1Z.PV_RunJoin_RetryProjection32
set_option autoImplicit false
namespace R1Z.PV_RunJoin_AttemptProjection32
open Aeneas Aeneas.Std Result PV_RunJoin_UnifiedRetry ProverCommitSemanticTransport26
variable [ProverRwFull.ExternalTypes] [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]
variable {N L C N' L' C' : Type}
variable (project : State N L C → State N' L' C')
    (left : ProverRwEffectCallback.Account (State N L C))
    (right : ProverRwEffectCallback.Account (State N' L' C'))
    (bodyA : Body (State N L C)) (bodyB : Body (State N' L' C'))
    (entropy_step : ∀ index s,
      mapR (fun out => (out.1,project out.2)) (entropy left index s) = entropy right index (project s))
    (body_step : ∀ secret s,
      mapR (fun out => (out.1,project out.2)) (bodyA secret s) = bodyB secret (project s))
include entropy_step body_step

/-- Complete entropy and body simulations compose in actual callback order;
only Rejected retries. The common secret and current returned world are used. -/
theorem step (index : Nat) (s : State N L C) :
    mapR (fun out => (out.1,project out.2)) (attempt left bodyA index s) =
      attempt right bodyB index (project s) := by
  unfold attempt
  rw [← entropy_step index s]
  cases he : entropy left index s with
  | fail e => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨status,next⟩
    cases status with
    | Err e => rfl
    | Ok secret =>
      simp only [mapR,bind_tc_ok,Aeneas.Std.uncurry]
      rw [← body_step secret next]
      cases hb : bodyA secret next with
      | fail e => rfl
      | div => rfl
      | ok pair =>
        rcases pair with ⟨status,final⟩
        cases status with
        | Ok proof => rfl
        | Err e => cases e <;> rfl
#print axioms step

theorem client (s : State N L C) :
    mapR (fun out => (out.1,project out.2)) (PV_RunJoin_UnifiedRetry.client left bodyA s) =
      PV_RunJoin_UnifiedRetry.client right bodyB (project s) :=
  PV_RunJoin_RetryProjection32.eight project _ _
    (step project left right bodyA bodyB entropy_step body_step) s
#print axioms client
end R1Z.PV_RunJoin_AttemptProjection32
