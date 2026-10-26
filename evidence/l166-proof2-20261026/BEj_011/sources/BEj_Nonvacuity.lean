import BEj_LocalExport
import BEf_Count
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEj_Nonvacuity
open Aeneas Aeneas.Std Result SdkC_Source

/-- Local weak observation does not require rejected final-state equality.
This concrete positive-query execution changes state and retains the failed
attempt. No physical native execution is manufactured by this example. -/
theorem failed_attempt (parts : Parts) (n : Nat) (before : Log) :
    let code : Code (core.result.Result Unit Unit) := .read parts (fun _ => .done (.Ok ()))
    let call := BEf_Count.call (fun _ => .fail .panic)
    BEh_Scope.Law (E := Unit) (.fail .panic,n+2,before ++ [⟨parts,.fail .panic⟩])
      (BEf_Carrier.run call code n before) ∧
    BEi_RecorderCut.issued before (before ++ [⟨parts,.fail .panic⟩]) =
      [⟨parts,.fail .panic⟩] := by
  dsimp only
  refine ⟨⟨⟨?_,?_⟩,⟨Iff.rfl,fun _ => rfl⟩⟩,?_⟩
  · intro a
    constructor <;> intro h <;> cases h
  · intro a h
    cases h
  · simp only [BEi_RecorderCut.issued,List.drop_left]

/-- Two identical addresses are two attempted occurrences, even when the
second digest fails. The final failure does not roll back the first read. -/
theorem duplicate_failed (parts : Parts) (digest : Digest) (before : Log) :
    let code : Code (core.result.Result Unit Unit) :=
      .read parts (fun _ => .read parts (fun _ => .done (.Ok ())))
    let call : Parts → Nat → Result Digest × Nat := fun _ n =>
      (if n = 0 then .ok digest else .fail .panic,n+1)
    BEf_Carrier.run call code 0 before =
      (.fail .panic,2,(before ++ [⟨parts,.ok digest⟩]) ++ [⟨parts,.fail .panic⟩]) ∧
    BEi_RecorderCut.issued before
      ((before ++ [⟨parts,.ok digest⟩]) ++ [⟨parts,.fail .panic⟩]) =
        [⟨parts,.ok digest⟩,⟨parts,.fail .panic⟩] := by
  refine ⟨rfl,?_⟩
  simp only [List.append_assoc,BEi_RecorderCut.issued,List.drop_left,List.cons_append,List.nil_append]

#print axioms failed_attempt
#print axioms duplicate_failed
end AspisR1.BEj_Nonvacuity
end
