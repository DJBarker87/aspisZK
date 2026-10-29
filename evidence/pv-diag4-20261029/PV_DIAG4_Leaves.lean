import PV_DIAG3_Capture
import PV_DIAG3_Drop
/-! Complete source bodies with no opaque callees: std 1.94.1
Backtrace::status, sys::stdio::Stderr::{new,is_write_vectored,flush}, and
panic_output. Carrier concerns diagnostic emissions, not total machine timing.
Borrowed discriminant reads and enum construction sit at V370. -/
set_option autoImplicit false
namespace PV_DIAG4
open PV_DIAG3
variable {S : Type}
inductive Status where | unsupported | disabled | captured
 deriving DecidableEq, Repr
-- The captured payload stays borrowed; this match neither forces nor drops it.
def status (trace : TraceValue) : Op S Status := fun s =>
 match trace with
 | .unsupported => ⟨[],s,.value .unsupported⟩
 | .disabled => ⟨[],s,.value .disabled⟩
 | .captured _ _ => ⟨[],s,.value .captured⟩
def statusCode : Status → Nat
 | .unsupported => 0 | .disabled => 1 | .captured => 2
def rawStderrNew : Op S Unit := PV_DIAG3.pure ()
def rawIsWriteVectored : Op S Bool := PV_DIAG3.pure true
def rawFlush : Op S (Except Unit Unit) := PV_DIAG3.pure (.ok ())
def panicOutput : Op S (Option Unit) :=
 sequence rawStderrNew (fun stderr => PV_DIAG3.pure (some stderr))
theorem status_exact (trace : TraceValue) (s : S) :
 status trace s = ⟨[],s,.value (match trace with
 | .unsupported => .unsupported | .disabled => .disabled | .captured _ _ => .captured)⟩ := by
 cases trace <;> rfl
#print axioms status_exact
theorem status_refines (trace : TraceValue) (s : S) :
 bind (status trace s) (fun result => PV_DIAG3.pure (statusCode result)) =
 PV_DIAG3.pure (traceStatus trace) s := by cases trace <;> rfl
#print axioms status_refines
theorem status_no_diagnostics (trace : TraceValue) (s : S) :
 (status trace s).events = [] := by cases trace <;> rfl
#print axioms status_no_diagnostics
theorem status_preserves_state (trace : TraceValue) (s : S) :
 (status trace s).state = s := by cases trace <;> rfl
#print axioms status_preserves_state
theorem status_captured_ignores_payload (a b : List Frame) (i j : Nat) :
 (status (.captured a i) : Op S Status) = status (.captured b j) := rfl
#print axioms status_captured_ignores_payload
theorem raw_flush_exact (s : S) : rawFlush s = ⟨[],s,.value (.ok ())⟩ := rfl
#print axioms raw_flush_exact
theorem raw_stderr_new_exact (s : S) : rawStderrNew s = ⟨[],s,.value ()⟩ := rfl
#print axioms raw_stderr_new_exact
theorem raw_vectored_exact (s : S) : rawIsWriteVectored s = ⟨[],s,.value true⟩ := rfl
#print axioms raw_vectored_exact
theorem panic_output_exact (s : S) : panicOutput s = ⟨[],s,.value (some ())⟩ := rfl
#print axioms panic_output_exact
end PV_DIAG4
