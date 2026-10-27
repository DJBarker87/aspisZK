import BEl_Recorder
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_PartialRecorder
open Aeneas Aeneas.Std Result SdkC_Source

/-- A nonreturning backend leaves its pre-entry attempted record pending. -/
def run {S A : Type} (call : Parts → S → Result Digest × S) : Code A → S →
    BEl_Recorder.History → Result A × S × BEl_Recorder.History
  | .done a, state, before => (.ok a,state,before)
  | .step r k, state, before => match r with
    | .ok a => run call (k a) state before
    | .fail e => (.fail e,state,before)
    | .div => (.div,state,before)
  | .read parts k, state, before =>
    let (answer,next) := call parts state
    match answer with
    | .ok digest => run call (k digest) next (BEl_Recorder.complete before parts (.ok digest))
    | .fail e => (.fail e,next,BEl_Recorder.enter before parts)
    | .div => (.div,next,BEl_Recorder.enter before parts)

/-- The ambient observed stop labels the pending attempt. It is not a Rust
returned error. This decoder is valid for runs from completed initial histories;
it is not injective on arbitrary independently decorated histories. -/
def decode (stopped : Result Digest) (history : BEl_Recorder.History) : Log :=
  history.map (fun attempt => ⟨attempt.parts,attempt.returned.getD stopped⟩)

def stop {A : Type} : Result A → Result Digest
  | .ok _ => .div
  | .fail e => .fail e
  | .div => .div

def observation {S A : Type} (out : Result A × S × BEl_Recorder.History) : Result A × S × Log :=
  (out.1,out.2.1,decode (stop out.1) out.2.2)

theorem decode_completed (stopped : Result Digest) (before : Log) :
    decode stopped (BEl_Recorder.completed before) = before := by
  induction before with
  | nil => rfl
  | cons query rest ih =>
    simpa only [decode,BEl_Recorder.completed,List.map_cons,Option.getD_some] using
      congrArg (List.cons query) ih

theorem decode_enter (stopped : Result Digest) (before : Log) (parts : Parts) :
    decode stopped (BEl_Recorder.enter (BEl_Recorder.completed before) parts) =
      before ++ [⟨parts,stopped⟩] := by
  simp only [decode,BEl_Recorder.enter,List.map_append,List.map_cons,List.map_nil,Option.getD_none]
  exact congrArg (· ++ [⟨parts,stopped⟩]) (decode_completed stopped before)

/-- Full abstract per-call observation, including pending failing/diverging
attempts. The physical Rust/runtime extraction of call remains a separate gate. -/
theorem correspondence {S A : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (state : S) (before : Log) :
    observation (run call code state (BEl_Recorder.completed before)) =
      BEf_Carrier.run call code state before := by
  induction code generalizing state before with
  | done a =>
    simp only [run,observation,BEf_Carrier.run,stop,decode_completed]
  | step r k ih =>
    cases r with
    | ok a => exact ih a state before
    | fail e => simp only [run,observation,BEf_Carrier.run,stop,decode_completed]
    | div => simp only [run,observation,BEf_Carrier.run,stop,decode_completed]
  | read parts k ih =>
    cases called : call parts state with
    | mk answer next =>
      cases answer with
      | ok digest =>
        simp only [run,BEf_Carrier.run,called]
        rw [←BEl_Recorder.completed_append]
        exact ih digest next (before ++ [⟨parts,.ok digest⟩])
      | fail e => simp only [run,BEf_Carrier.run,called,observation,stop,decode_enter]
      | div => simp only [run,BEf_Carrier.run,called,observation,stop,decode_enter]

#print axioms decode_completed
#print axioms decode_enter
#print axioms correspondence
end AspisR1.BEl_PartialRecorder
end
