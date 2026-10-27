import BEl_PartialRecorder
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_PrefixRecorder
open Aeneas Aeneas.Std Result SdkC_Source
open BEl_Recorder BEl_PartialRecorder

/-- A private local recorder can be appended to an existing physical history.
This is a recorder law, not a bridge from a value-only extraction. -/
theorem run_prefix {S A : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (state : S) (prior history : History) :
    run call code state (prior ++ history) =
      let out := run call code state history
      (out.1,out.2.1,prior ++ out.2.2) := by
  induction code generalizing state history with
  | done a => rfl
  | step r k ih =>
    cases r with
    | ok a => exact ih a state history
    | fail e => rfl
    | div => rfl
  | read parts k ih =>
    cases called : call parts state with
    | mk answer next =>
      cases answer with
      | ok digest =>
        simp only [run,called,complete,List.append_assoc]
        exact ih digest next (history ++ [⟨parts,some (.ok digest)⟩])
      | fail e => simp only [run,called,enter,List.append_assoc]
      | div => simp only [run,called,enter,List.append_assoc]

theorem decode_prefix (stopped : Result Digest) (prior : Log) (history : History) :
    decode stopped (completed prior ++ history) = prior ++ decode stopped history := by
  simp only [decode,List.map_append]
  exact congrArg (· ++ decode stopped history) (decode_completed stopped prior)

/-- Fresh local observation and pre-existing source history have the same
ordered attempts, including the final pending attempt on nonreturn. -/
theorem observation_prefix {S A : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (state : S) (prior : Log) :
    observation (run call code state (completed prior)) =
      let out := observation (run call code state [])
      (out.1,out.2.1,prior ++ out.2.2) := by
  have h := run_prefix call code state (completed prior) []
  simp only [List.append_nil] at h
  rw [h]
  simp only [observation,decode_prefix]

#print axioms run_prefix
#print axioms decode_prefix
#print axioms observation_prefix
end AspisR1.BEl_PrefixRecorder
end
