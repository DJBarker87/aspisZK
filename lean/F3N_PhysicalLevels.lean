import F3N_PhysicalRows
import Port9OR_P6Levels
set_option autoImplicit false
namespace AspisR1.F3N_PhysicalLevels
open Aeneas Aeneas.Std Result MultiproofConeRef
open F3N_PhysicalCode

theorem level (s : reference.Scratch) (physical : Slice U8) :
    lower (Port9OR_P6Levels.level s physical)=MultiproofConePhysicalLevels.level s physical :=
  F3N_PhysicalRows.rows s.n.val s physical 0#usize 0#usize

theorem levels (height : Nat) (s : reference.Scratch) (physical : Slice U8) :
    lower (Port9OR_P6Levels.levels height s physical)=MultiproofConePhysicalLevels.levels height s physical := by
  induction height generalizing s with
  | zero=>rfl
  | succ height ih=>
    rw [Port9OR_P6Levels.levels,F3N_PhysicalBind.bind,level,MultiproofConePhysicalLevels.levels]
    unfold MultiproofConePhysicalLevels.bindRun
    congr 1
    funext r
    cases r with
    | fail e=>rfl
    | div=>rfl
    | ok out=>cases out with
      | Stop stopped=>rfl
      | Done after=>exact ih after

#print axioms level
#print axioms levels
end AspisR1.F3N_PhysicalLevels
