import PFin_LeafBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_HashLeavesBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortFrozenOrder PFin_AddressBound

theorem leaves (p : Parsed) (q : Fin 22 → Fin 262144) (kind : Nat) (positions : List Nat) (rev : Live) :
    Bounded (hashLeaves p q kind positions rev) := by
  induction positions generalizing rev with
  | nil => exact done _
  | cons pos rest ih =>
    unfold hashLeaves
    apply ask _ _ (PFin_LeafBound.leaf p kind pos)
    intro digest
    cases rev with
    | nil => exact ih _
    | cons head tail =>
      obtain ⟨j,value⟩ := head
      split
      · split
        · exact ih _
        · exact done _
      · exact ih _

#print axioms leaves
end AspisR1.PFin_HashLeavesBound
end
