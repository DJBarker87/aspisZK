import PV_DIAG2_Exit
set_option autoImplicit false
namespace PV_DIAG2
open Aeneas Aeneas.Std Result
open R1Z ProverCommitRetry34

structure Process (S P : Type) where
 retryResult : Result (Step (Published P) × S)
 observed : Execution Nat

/-- Actual formatter, capture, write, stdout, and runtime continuations must
supply their complete effects and terminal behavior. In particular, invoking
reporting is not silently assumed to return normally. These are data inputs;
the native equalities and their joint public law remain explicit P obligations. -/
def process {S P : Type} (x : Observed (Step (Published P) × S))
    (report : PV_DIAG2.Error → Execution Nat)
    (success : Published P → S → Execution Nat)
    (runtime : Aeneas.Std.Error → Execution Nat)
    (divergence unexpectedRetry : Execution Nat) : Process S P :=
 ⟨x.result, prepend x.effects (match x.result with
 | .ok (.stop e,_) => report (exportError e)
 | .ok (.done p,s) => success p s
 | .ok (.retry,_) => unexpectedRetry
 | .fail e => runtime e
 | .div => divergence)⟩

theorem process_retains_result {S P : Type}
    (x : Observed (Step (Published P) × S)) (r : PV_DIAG2.Error → Execution Nat)
    (s : Published P → S → Execution Nat) (f : Aeneas.Std.Error → Execution Nat)
    (d u : Execution Nat) : (process x r s f d u).retryResult = x.result := rfl

/-- This statement includes an OOM inside plan::err or backtrace formatting;
it does not replace the OOM with a normally returned Error message. -/
theorem reporting_oom_retained {S P : Type}
    (x : Observed (Step (Published P) × S)) (e : ProverCommitRetry34.Error) (after : S)
    (h : x.result = ok (.stop e,after))
    (r : PV_DIAG2.Error → Execution Nat) (size : Nat) (pcs : List Nat) (events : List Effect)
    (oom : r (exportError e) = ⟨events,.oom size pcs⟩)
    (s : Published P → S → Execution Nat) (f : Aeneas.Std.Error → Execution Nat)
    (d u : Execution Nat) :
 (process x r s f d u).observed = ⟨x.effects ++ events,.oom size pcs⟩ := by
 simp only [process,h,oom,prepend]

theorem reporting_panic_retained {S P : Type}
    (x : Observed (Step (Published P) × S)) (e : ProverCommitRetry34.Error) (after : S)
    (h : x.result = ok (.stop e,after))
    (r : PV_DIAG2.Error → Execution Nat) (msg : String) (pcs : List Nat) (events : List Effect)
    (panic : r (exportError e) = ⟨events,.panic msg pcs⟩)
    (s : Published P → S → Execution Nat) (f : Aeneas.Std.Error → Execution Nat)
    (d u : Execution Nat) :
 (process x r s f d u).observed = ⟨x.effects ++ events,.panic msg pcs⟩ := by
 simp only [process,h,panic,prepend]

/-- The fixed stderr-request theorem applies only when native reporting
completes with this execution. It is not a hidden no-OOM premise. -/
theorem normal_report_request {S P : Type}
    (x : Observed (Step (Published P) × S)) (e : ProverCommitRetry34.Error) (after : S)
    (h : x.result = ok (.stop e,after)) (pcs : List Nat)
    (s : Published P → S → Execution Nat) (f : Aeneas.Std.Error → Execution Nat)
    (d u : Execution Nat) :
 (process x (fun e => reportError e pcs "" false) s f d u).observed =
 ⟨x.effects ++ [.returned (exportError e),
  .stderr ("Error: " ++ spelling (exportError e) ++ "\n")],.value 1⟩ := by
 simp only [process,h,report_disabled,prepend]

#print axioms process_retains_result
#print axioms reporting_oom_retained
#print axioms reporting_panic_retained
#print axioms normal_report_request
end PV_DIAG2
