import BEl_Recorder
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_ReturnRecorder
open Aeneas Aeneas.Std Result SdkC_Source

/-- Model of the recording wrapper for an infallibly returning backend.
This is only the returned-call semantics, not an extraction of physical Rust. -/
def run {A : Type} (hash : Parts → Digest) : Code A → BEl_Recorder.History →
    Result A × BEl_Recorder.History
  | .done a, before => (.ok a,before)
  | .step r k, before => match r with
    | .ok a => run hash (k a) before
    | .fail e => (.fail e,before)
    | .div => (.div,before)
  | .read parts k, before =>
    run hash (k (hash parts)) (BEl_Recorder.complete before parts (.ok (hash parts)))

/-- Exact value and completed-record equality for arbitrary effect syntax.
No local success is assumed; pure rejection and repeated inputs remain. -/
theorem correspondence {A : Type} (hash : Parts → Digest) (code : Code A) (before : Log) :
    run hash code (BEl_Recorder.completed before) =
      ((SdkC_Source.run (fun p => .ok (hash p)) code before).1,
       BEl_Recorder.completed (SdkC_Source.run (fun p => .ok (hash p)) code before).2) := by
  induction code generalizing before with
  | done a => rfl
  | step r k ih =>
    cases r with
    | ok a => exact ih a before
    | fail e => rfl
    | div => rfl
  | read parts k ih =>
    simp only [run,SdkC_Source.run]
    rw [←BEl_Recorder.completed_append]
    exact ih (hash parts) (before ++ [⟨parts,.ok (hash parts)⟩])

#print axioms correspondence
end AspisR1.BEl_ReturnRecorder
end
