import PV_L1D_CallbackSafe
import PV_L1D_RetryFold
set_option autoImplicit false
namespace PV_L1D_RetryCount
open Aeneas Aeneas.Std Result
open PV_L1D_Logged PV_L1D_CallbackSafe
open R1Z.ProverCommitRetry34 (Published)
variable {S P : Type}
/-- Exact callback count of the logged recursion, conditional only on the
per-attempt entry association. This does not assert that native leaf logs
satisfy that association. Failures/divergence are retained by RetryFold. -/
theorem successful_callbacks (a : PV_L1D_RetryFold.Attempt S P)
    (entries : ∀ k s, callbacks (a k s).events = [k])
    (n k : Nat) (s after : S) (p : Published P)
    (h : (PV_L1D_RetryFold.run a n k s).result = .ok (.done p,after)) :
    p.attempts = k + (callbacks (PV_L1D_RetryFold.run a n k s).events).length := by
  induction n generalizing k s after p with
  | zero => cases h
  | succ n ih =>
    cases step : a k s with
    | mk es status =>
      have hc : callbacks es = [k] := by simpa only [step] using entries k s
      simp only [PV_L1D_RetryFold.run,step] at h ⊢
      cases status with
      | fail e => cases h
      | div => cases h
      | ok pair =>
        rcases pair with ⟨out,next⟩
        cases out with
        | done proof =>
          have hp : (Published.mk proof (k+1) : Published P) = p := by
            change (.ok (.done ⟨proof,k+1⟩,next) : Result (R1Z.ProverCommitRetry34.Step (Published P) × S)) = .ok (.done p,after) at h
            cases h
            rfl
          cases hp
          change k+1 = k + (callbacks (es ++ [])).length
          rw [callbacks_append,hc]
          rfl
        | stop e =>
          change (.ok (.stop e,next) : Result (R1Z.ProverCommitRetry34.Step (Published P) × S)) = .ok (.done p,after) at h
          cases h
        | retry =>
          change (PV_L1D_RetryFold.run a n (k+1) next).result = .ok (.done p,after) at h
          have rest := ih (k+1) next after p h
          change p.attempts = k + (callbacks (es ++ (PV_L1D_RetryFold.run a n (k+1) next).events)).length
          rw [callbacks_append,hc,List.length_append,List.length_singleton]
          omega
#print axioms successful_callbacks
end PV_L1D_RetryCount
