import PV_L1D_ResultCoercion
set_option autoImplicit false
namespace PV_L1D_RetryFold
open Aeneas Aeneas.Std Result
open R1Z.ProverCommitRetry34 (Step Published)
open PV_L1D_Logged
variable {S P : Type}
abbrev Attempt (S P : Type) := Nat → S → Logged (Step P × S)
/-- Retain each leaf's prefix on every retry and outer failure/divergence.
The recursion does not coerce an opaque recursive source call into Logged. -/
def run (a : Attempt S P) : Nat → Nat → S → Logged (Step (Published P) × S)
  | 0, _, s => pure (.stop .AttemptsExhausted,s)
  | n+1, k, s => do
    let (out,after) ← a k s
    match out with
    | .done p => pure (.done ⟨p,k+1⟩,after)
    | .stop e => pure (.stop e,after)
    | .retry => run a n (k+1) after

theorem erasure (a : Attempt S P) (n k : Nat) (s : S) :
    erase (run a n k s) =
      R1Z.ProverCommitRetry34.run (fun j st => erase (a j st)) n k s := by
  induction n generalizing k s with
  | zero => rfl
  | succ n ih =>
    simp only [run,erase_bind,R1Z.ProverCommitRetry34.run]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    rintro ⟨out,after⟩ called
    cases out with
    | done p => rfl
    | stop e => rfl
    | retry => exact ih (k+1) after
#print axioms erasure

/-- A retry keeps the earlier ordered word even when the suffix aborts. -/
theorem retry_events (a : Attempt S P) (n k : Nat) (s after : S)
    (es : List R1Z.SideChannelL1AttemptRecord.Event)
    (h : a k s = ⟨es,.ok (.retry,after)⟩) :
    (run a (n+1) k s).events = es ++ (run a n (k+1) after).events := by
  simp only [run,h]
  rfl
#print axioms retry_events

theorem failure_prefix (a : Attempt S P) (n k : Nat) (s : S)
    (es : List R1Z.SideChannelL1AttemptRecord.Event) (e : Aeneas.Error)
    (h : a k s = ⟨es,.fail e⟩) :
    (run a (n+1) k s).events = es := by
  simp only [run,h]
  rfl
#print axioms failure_prefix
end PV_L1D_RetryFold
