import PV_DIAG2_Effects
/-! Deployed rust-src 1.94.1 process.rs/stdio.rs outer control flow.
Leaf executions include their own temporaries/unwind. Error drop after a
normal write is separate. An abnormal reporter is handed to the enclosing
error/unwind continuation; it is never replaced by a successful ExitCode.
This is an open operational interface, not a proof of the leaf executions. -/
set_option autoImplicit false
namespace PV_DIAG2

def pureExecution {A : Type} (a : A) : Execution A := ⟨[],.value a⟩

/-- std's capture check precedes the global write. `globalWrite` includes
write_fmt's Result drop and the temporary Stderr handle drop, on every exit. -/
def attemptPrint (capture : Execution Bool) (globalWrite : Execution Unit) : Execution Unit :=
 bind capture (fun captured => if captured then pureExecution () else globalWrite)

/-- Complete cleanup on an abnormal reporter is supplied explicitly. On
normal return, err is dropped before ExitCode::FAILURE leaves this frame. -/
def terminateOwned {E : Type} (result : Except E Unit)
    (report : E → Execution Unit) (dropError : E → Execution Unit)
    (unwindError : E → Terminal Unit → Execution Nat) : Execution Nat :=
 match result with
 | .ok () => pureExecution 0
 | .error e =>
   let body := report e
   prepend body.effects (match body.terminal with
    | .value () => bind (dropError e) (fun _ => pureExecution 1)
    | abnormal => unwindError e abnormal)

theorem termination_success {E : Type} (r d : E → Execution Unit)
    (u : E → Terminal Unit → Execution Nat) :
 terminateOwned (.ok ()) r d u = ⟨[],.value 0⟩ := rfl

/-- A successful capture path does not call the global stderr writer. All
capture-buffer effects are retained, including formatting and locking. -/
theorem captured_no_global (events : List Effect) (w : Execution Unit) :
 attemptPrint ⟨events,.value true⟩ w = ⟨events,.value ()⟩ := by
 simp [attemptPrint,bind,prepend,pureExecution]

theorem uncaptured_global (events : List Effect) (w : Execution Unit) :
 attemptPrint ⟨events,.value false⟩ w = prepend events w := rfl

theorem capture_panic (events : List Effect) (msg : String) (pcs : List Nat)
    (w : Execution Unit) :
 attemptPrint ⟨events,.panic msg pcs⟩ w = ⟨events,.panic msg pcs⟩ := rfl

theorem capture_oom (events : List Effect) (size : Nat) (pcs : List Nat)
    (w : Execution Unit) :
 attemptPrint ⟨events,.oom size pcs⟩ w = ⟨events,.oom size pcs⟩ := rfl

/-- Ignoring a returned I/O error does not erase write or destructor effects.
No assumption is made that the destructor is silent or returns normally. -/
def ignoreWriteResult {I : Type} (w : Execution (Except I Unit))
    (dropResult : Except I Unit → Execution Unit) : Execution Unit := bind w dropResult

theorem ignored_io_error {I : Type} (events : List Effect) (err : I)
    (dropResult : Except I Unit → Execution Unit) :
 ignoreWriteResult ⟨events,.value (.error err)⟩ dropResult =
 prepend events (dropResult (.error err)) := rfl

theorem report_then_drop {E : Type} (e : E) (r d : E → Execution Unit)
    (u : E → Terminal Unit → Execution Nat) (events : List Effect)
    (hr : r e = ⟨events,.value ()⟩) :
 terminateOwned (.error e) r d u =
 prepend events (bind (d e) (fun _ => pureExecution 1)) := by
 simp only [terminateOwned,hr]

/-- Native cleanup/unwind is retained, with the prior formatter prefix. -/
theorem report_panics_unwind {E : Type} (e : E) (r d : E → Execution Unit)
    (u : E → Terminal Unit → Execution Nat) (events : List Effect)
    (msg : String) (pcs : List Nat) (hr : r e = ⟨events,.panic msg pcs⟩) :
 terminateOwned (.error e) r d u = prepend events (u e (.panic msg pcs)) := by
 simp only [terminateOwned,hr]

/-- Normal error exit after arbitrary successful capture/write and drop.
This conclusion retains the caller's full pre-existing effect history. -/
theorem normal_error_exit {E : Type} (e : E) (r d : E → Execution Unit)
    (u : E → Terminal Unit → Execution Nat) (before after : List Effect)
    (hr : r e = ⟨before,.value ()⟩) (hd : d e = ⟨after,.value ()⟩) :
 terminateOwned (.error e) r d u = ⟨before ++ after,.value 1⟩ := by
 simp [terminateOwned,hr,hd,bind,prepend,pureExecution]

#print axioms termination_success
#print axioms captured_no_global
#print axioms uncaptured_global
#print axioms capture_panic
#print axioms capture_oom
#print axioms ignored_io_error
#print axioms report_then_drop
#print axioms report_panics_unwind
#print axioms normal_error_exit
end PV_DIAG2
