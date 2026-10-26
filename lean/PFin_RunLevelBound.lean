import PFin_HashLeavesBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_RunLevelBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortFrozenOrder PFin_AddressBound
attribute [local instance] Classical.propDecidable

theorem level (fuel : Nat) (live : Live) (nodes : Bytes) : Bounded (runLevel fuel live nodes) := by
  induction fuel generalizing live nodes with
  | zero => exact done _
  | succ fuel ih =>
    cases live with
    | nil => exact done _
    | cons head rest =>
      obtain ⟨i,value⟩ := head
      unfold runLevel
      dsimp only
      split_ifs
      all_goals
        repeat' first
          | exact done _
          | (apply ask _ _ (by rw [BinMerkle32Path.nodeInput_length];decide)
             intro digest
             exact PFin_AddressBound.bind _ _ (ih _ _) (fun _=>done _))
          | split

theorem levels (height : Nat) (live : Live) (nodes : Bytes) : Bounded (runLevels height live nodes) := by
  induction height generalizing live nodes with
  | zero => exact done _
  | succ height ih =>
    apply PFin_AddressBound.bind _ _ (level _ _ _)
    intro result
    cases result with
    | none => exact done _
    | some pair => exact ih _ _

#print axioms level
#print axioms levels
end AspisR1.PFin_RunLevelBound
end
