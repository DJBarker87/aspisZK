import R1Z.ProverCommitPublish43
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19AssemblyLength
open ProverCommitPublish43
attribute [local instance] Classical.propDecidable

-- Inspect the final guard symbolically, never evaluate a concrete proof.
theorem assemble (front : Except Error Bytes) (ps : List QueryParts)
    (ss : List Slot) (offset size : Nat) (result : Bytes)
    (success : ProverCommitPublish43.assemble front ps ss offset size = .ok result) :
    result.length = size := by
  unfold ProverCommitPublish43.assemble at success
  cases front with
  | error e => cases success
  | ok first =>
    change (if (queries ps first).length ≠ offset then Except.error Error.parse else
      (slots ss (queries ps first)).bind (fun final =>
        if final.length ≠ size then Except.error Error.parse else Except.ok final)) = Except.ok result at success
    split at success
    · cases success
    · cases hs : slots ss (queries ps first) with
      | error e =>
        rw [hs] at success
        cases success
      | ok final =>
        rw [hs] at success
        change (if final.length ≠ size then Except.error Error.parse else Except.ok final) = Except.ok result at success
        split at success
        · cases success
        · have same : final = result := Except.ok.inj success
          subst result
          omega

#print axioms assemble
end R1Z.ProverRw19AssemblyLength
