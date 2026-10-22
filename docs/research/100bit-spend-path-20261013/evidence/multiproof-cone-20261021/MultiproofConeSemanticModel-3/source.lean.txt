import MultiproofConeFrameModel
import MultiproofConeLogicalPayload

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeSemanticModel
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft MultiproofConeFrameModel MultiproofConeLogicalPayload
attribute [local instance] Classical.propDecidable

/-- The frozen row recurrence in exactly the guard/continuation form used to
compare the extracted owned parser. No wire or recurrence is evaluated. -/
theorem row_step (fuel row : Nat) (wire : Bytes) :
    semanticRows (fuel+1) row wire =
      if wire.length<5+storedSize row then none else
      if wire.take 5≠headerBytes row then none else
      if 14≤row ∧ ¬canonical (slice wire 5 (storedSize row)) then none else
      (semanticRows fuel (row+1) (wire.drop (5+storedSize row))).map
        (fun tail => (wire.take 5 ++ logicalBytes row (slice wire 5 (storedSize row)))::tail) := by
  rw [semanticRows]
  dsimp only [storedSize,headerBytes,logicalBytes]
  generalize ht : semanticRows fuel (row+1)
    (wire.drop (5+if 14≤row then (rowShape row).2/2 else (rowShape row).2)) = tail
  cases tail <;> split_ifs <;> rfl

#print axioms row_step
end AspisR1.MultiproofConeSemanticModel
end
