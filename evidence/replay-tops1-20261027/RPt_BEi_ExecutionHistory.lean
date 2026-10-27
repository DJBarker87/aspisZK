import RPt_BEi_ExecutionUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEi_ExecutionHistory
open Aeneas Aeneas.Std Result SdkC_Source BEi_Execution

/-- Appending the same chronological prefix changes no control or carrier. -/
theorem prepend {S A : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (state after : S) (before log prior : Log) (value : Result A)
    (execution : Executes call code state before value after log) :
    Executes call code state (prior ++ before) value after (prior ++ log) := by
  induction execution with
  | done => exact .done _ _ _
  | stepOk a k state after before log value next ih => exact .stepOk _ _ _ _ _ _ _ ih
  | stepFail => exact .stepFail _ _ _ _
  | stepDiv => exact .stepDiv _ _ _
  | readOk parts k state middle after before log digest value called next ih =>
    apply Executes.readOk parts k state middle after (prior ++ before) (prior ++ log) digest value called
    simpa only [List.append_assoc] using ih
  | readFail parts k state after before error called =>
    simpa only [List.append_assoc] using
      Executes.readFail parts k state after (prior ++ before) error called
  | readDiv parts k state after before called =>
    simpa only [List.append_assoc] using
      Executes.readDiv parts k state after (prior ++ before) called

/-- Every operational execution retains the entire pre-cut recorder. -/
theorem retained {S A : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (state after : S) (before log : Log) (value : Result A)
    (execution : Executes call code state before value after log) :
    ∃ issued, log = before ++ issued := by
  induction execution with
  | done => exact ⟨[],(List.append_nil _).symm⟩
  | stepOk a k state after before log value next ih => exact ih
  | stepFail => exact ⟨[],(List.append_nil _).symm⟩
  | stepDiv => exact ⟨[],(List.append_nil _).symm⟩
  | readOk parts k state middle after before log digest value called next ih =>
    obtain ⟨issued,same⟩ := ih
    exact ⟨⟨parts,.ok digest⟩ :: issued,by simpa only [List.append_assoc,List.singleton_append] using same⟩
  | readFail => exact ⟨[_],rfl⟩
  | readDiv => exact ⟨[_],rfl⟩

#print axioms prepend
#print axioms retained
end AspisR1.BEi_ExecutionHistory
end
