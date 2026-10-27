import RPt_BEl_Recorder
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_RawBackend
open Aeneas Aeneas.Std Result SdkC_Source

def call {S : Type} (backend : Parts → S → Digest × S) (parts : Parts) (state : S) :
    Result Digest × S := (.ok (backend parts state).1,(backend parts state).2)

/-- State-dependent raw replies model the Rust Digest32 return shape. The
explicit attempted recorder is outside every protocol Result. This remains
an operational reference model until its physical source correspondence passes. -/
def run {S A : Type} (backend : Parts → S → Digest × S) : Code A → S →
    BEl_Recorder.History → Result A × S × BEl_Recorder.History
  | .done a, state, before => (.ok a,state,before)
  | .step r k, state, before => match r with
    | .ok a => run backend (k a) state before
    | .fail e => (.fail e,state,before)
    | .div => (.div,state,before)
  | .read parts k, state, before =>
    let (answer,next) := backend parts state
    run backend (k answer) next (BEl_Recorder.complete before parts (.ok answer))

/-- No purity assumption: the same chronological backend state is threaded
through every returned read, including reads preceding a pure rejection. -/
theorem correspondence {S A : Type} (backend : Parts → S → Digest × S)
    (code : Code A) (state : S) (before : Log) :
    run backend code state (BEl_Recorder.completed before) =
      ((BEf_Carrier.run (call backend) code state before).1,
       (BEf_Carrier.run (call backend) code state before).2.1,
       BEl_Recorder.completed (BEf_Carrier.run (call backend) code state before).2.2) := by
  induction code generalizing state before with
  | done a => rfl
  | step r k ih =>
    cases r with
    | ok a => exact ih a state before
    | fail e => rfl
    | div => rfl
  | read parts k ih =>
    cases h : backend parts state with
    | mk answer next =>
      simp only [run,BEf_Carrier.run,call,h]
      rw [←BEl_Recorder.completed_append]
      exact ih answer next (before ++ [⟨parts,.ok answer⟩])

#print axioms correspondence
end AspisR1.BEl_RawBackend
end
