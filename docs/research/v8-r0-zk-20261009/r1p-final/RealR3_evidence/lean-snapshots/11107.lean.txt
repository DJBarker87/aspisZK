import R1Z.RealR3_SemanticEmission
/-! Byte-prefix transport by induction. Every error and returned state is
retained; no recurrence over concrete challenge values is reduced. The byte
prefix law is independent of any LegacyHashFn-to-oracle-machine binding. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.RealR3_EmissionPrefix
open Aeneas Aeneas.Std Result ProverCommitStateLift28 RealR3_SemanticEmission

/-- Adding a prior publication prefix commutes with the complete owned row
execution, including early semantic errors and all ordered oracle effects. -/
theorem prepend {S : Type} (effect : Unit → Parts → Port S Bytes32)
    (frames : List (U8 × Bytes)) (state : State) (lead acc : List U8) (machine : S) :
    rows effect frames state (lead ++ acc) machine = (do
      let ((value,next,bytes),after) ← rows effect frames state acc machine
      ok ((value,next,lead ++ bytes),after)) := by
  induction frames generalizing state acc machine with
  | nil => rfl
  | cons frame tail ih =>
    rcases frame with ⟨row,framed⟩
    simp only [rows,emit,bind_run]
    cases called : ProverCommitSemanticProgram28.semantic effect state row framed machine with
    | fail e => rfl
    | div => rfl
    | ok out =>
      rcases out with ⟨⟨value,next⟩,after⟩
      cases value with
      | Err e => rfl
      | Ok q =>
        change rows effect tail next ((lead ++ acc) ++ framed.val) after = (do
          let ((v,s,b),m) ← rows effect tail next (acc ++ framed.val) after
          ok ((v,s,lead ++ b),m))
        rw [List.append_assoc]
        exact ih next (acc ++ framed.val) after

#print axioms prepend
end R1Z.RealR3_EmissionPrefix
