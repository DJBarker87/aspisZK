import RPt_BEi_ExecutionComplete
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEi_ExecutionUnique
open Aeneas Aeneas.Std Result SdkC_Source BEi_Execution

theorem unique {S A : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (state leftState rightState : S) (before leftLog rightLog : Log)
    (left right : Result A)
    (first : Executes call code state before left leftState leftLog)
    (second : Executes call code state before right rightState rightLog) :
    left = right ∧ leftState = rightState ∧ leftLog = rightLog := by
  have same := (sound call code state leftState before leftLog left first).symm.trans
    (sound call code state rightState before rightLog right second)
  exact ⟨congrArg Prod.fst same,congrArg (fun x => x.2.1) same,
    congrArg (fun x => x.2.2) same⟩

/-- Separates the local transition evidence from the deterministic denotation. -/
theorem iff_run {S A : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (state after : S) (before log : Log) (value : Result A) :
    Executes call code state before value after log ↔
      BEf_Carrier.run call code state before = (value,after,log) := by
  constructor
  · exact sound call code state after before log value
  · intro same
    have run := BEi_ExecutionComplete.complete call code state before
    simpa only [same] using run

#print axioms unique
#print axioms iff_run
end AspisR1.BEi_ExecutionUnique
end
