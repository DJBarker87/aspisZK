import RPt_BEf_Carrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEk_Projection
open Aeneas Aeneas.Std Result SdkC_Source

/-- Common observable projection. It deliberately permits distinct physical
carriers and dead private scratch; log occurrences remain in source order. -/
def outcome {N S A : Type} (project : N → S) (out : Result A × N × Log) : Result A × S × Log :=
  (out.1,project out.2.1,out.2.2)

/-- Contextual source interpreter simulation from a SINGLE digest-step law.
This is not a proof that either interpreter is the physical shipped machine.
The missing physical extraction cannot be supplied by this theorem. -/
theorem run {N S A : Type} (project : N → S)
    (nativeCall : Parts → N → Result Digest × N)
    (sourceCall : Parts → S → Result Digest × S)
    (step : ∀ parts state, (nativeCall parts state).1 = (sourceCall parts (project state)).1 ∧
      project (nativeCall parts state).2 = (sourceCall parts (project state)).2)
    (code : Code A) (state : N) (before : Log) :
    outcome project (BEf_Carrier.run nativeCall code state before) =
      BEf_Carrier.run sourceCall code (project state) before := by
  induction code generalizing state before with
  | done value => rfl
  | step result next ih =>
    cases result with
    | ok value => exact ih value state before
    | fail error => rfl
    | div => rfl
  | read parts next ih =>
    obtain ⟨answer,carrier⟩ := step parts state
    cases called : nativeCall parts state with
    | mk result after =>
      have same : sourceCall parts (project state) = (result,project after) := by
        apply Prod.ext
        · exact answer.symm.trans (congrArg Prod.fst called)
        · exact carrier.symm.trans (congrArg project (congrArg Prod.snd called))
      cases result with
      | ok digest =>
        simpa only [BEf_Carrier.run,called,same] using ih digest after (before ++ [⟨parts,ok digest⟩])
      | fail error => simp only [BEf_Carrier.run,called,same,outcome]
      | div => simp only [BEf_Carrier.run,called,same,outcome]

#print axioms run
end AspisR1.BEk_Projection
end
