import PV_L1F_WorldLog
import PV_L1D_RetryFold
set_option autoImplicit false
namespace PV_L1G_WorldRetry
open R1Z.PV_W_Threading
open R1Z.ProverCommitRetry34 (Step Published)
variable {W S P : Type}
abbrev Event := R1Z.SideChannelL1AttemptRecord.Event
/-- Each leaf supplies a full independently retained world execution. No leaf
is replaced by a silent Result lift. Native adequacy is still required. -/
abbrev Attempt (W S P : Type) := Nat → S → M W Event Aeneas.Std.Error (Step P × S)
def run (a : Attempt W S P) : Nat → Nat → S → M W Event Aeneas.Std.Error (Step (Published P) × S)
 | 0, _, s => lift (.ok (.stop .AttemptsExhausted,s))
 | n+1, k, s => bind (a k s) fun (out,after) =>
   match out with
   | .done p => lift (.ok (.done ⟨p,k+1⟩,after))
   | .stop e => lift (.ok (.stop e,after))
   | .retry => run a n (k+1) after
/-- Auxiliary logging carries the post-world through successful retries.
The original full Run also retains that world on outer failure/divergence. -/
def stateAttempt (a : Attempt W S P) : PV_L1D_RetryFold.Attempt (W × S) P := fun k ws =>
 let r := a k ws.2 ws.1
 ⟨r.calls.map Prod.snd, match r.outcome with
 | .ok (out,s) => .ok (out,(r.world,s))
 | .fail e => .fail e
 | .div => .div⟩
def stateLog (r : Run W Event Aeneas.Std.Error (Step (Published P) × S)) :
 PV_L1D_Logged.Logged (Step (Published P) × (W × S)) :=
 ⟨r.calls.map Prod.snd, match r.outcome with
 | .ok (out,s) => .ok (out,(r.world,s))
 | .fail e => .fail e
 | .div => .div⟩
theorem failure_prefix (a : Attempt W S P) (n k : Nat) (s : S) (w : W)
 (e : Aeneas.Std.Error) (h : (a k s w).outcome = .fail e) :
 run a (n+1) k s w = ⟨.fail e,(a k s w).world,(a k s w).calls⟩ := by
 exact bind_fail _ _ w e h
#print axioms failure_prefix
theorem divergence_prefix (a : Attempt W S P) (n k : Nat) (s : S) (w : W)
 (h : (a k s w).outcome = .div) :
 run a (n+1) k s w = ⟨.div,(a k s w).world,(a k s w).calls⟩ := by
 exact bind_div _ _ w h
#print axioms divergence_prefix
end PV_L1G_WorldRetry
