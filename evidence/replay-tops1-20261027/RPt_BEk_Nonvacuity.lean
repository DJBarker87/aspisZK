import RPt_BEk_QueryPrefix
import RPt_BEk_LocalAssociation
import RPt_BEf_Count
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEk_Nonvacuity
open Aeneas Aeneas.Std Result SdkC_Source

/-- Two identical attempted addresses and a pure rejection are compatible
with deterministic replies. Rejected state/error identity is not required. -/
theorem rejected (parts : Parts) (digest : Digest) (n : Nat) (before : Log) :
    let code : Code (core.result.Result Unit Unit) :=
      .read parts (fun _ => .read parts (fun _ => .done (.Err ())))
    let log := (before ++ [⟨parts,ok digest⟩]) ++ [⟨parts,ok digest⟩]
    BEh_Scope.Law (E := Unit) (.fail .panic,n+9,log)
      (BEf_Carrier.run (BEf_Count.call (fun _ => ok digest)) code n before) ∧
    BEi_RecorderCut.issued before log = [⟨parts,ok digest⟩,⟨parts,ok digest⟩] := by
  dsimp only
  refine ⟨⟨⟨?_,?_⟩,⟨Iff.rfl,fun _ => rfl⟩⟩,?_⟩
  · intro a
    constructor <;> intro h <;> cases h
  · intro a h
    cases h
  · simp only [List.append_assoc,BEi_RecorderCut.issued,List.drop_left,List.cons_append,List.nil_append]

/-- The step-projection obligation is satisfiable with a changing private
component. No equality of unrelated machine pointers/private scratch is used. -/
theorem step (hashv : Parts → Result Digest) :
    ∀ parts (state : Nat × Bool),
      ((hashv parts,(state.1+1,!state.2)) : Result Digest × (Nat × Bool)).1 =
        (BEf_Count.call hashv parts state.1).1 ∧
      (((hashv parts,(state.1+1,!state.2)) : Result Digest × (Nat × Bool)).2).1 =
        (BEf_Count.call hashv parts state.1).2 := by
  intro parts state
  exact ⟨rfl,rfl⟩

#print axioms rejected
#print axioms step
end AspisR1.BEk_Nonvacuity
end
