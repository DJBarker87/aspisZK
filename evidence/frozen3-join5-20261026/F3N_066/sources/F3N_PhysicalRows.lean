import F3N_PhysicalNode
import F3N_PhysicalBind
import Port9OR_P6Rows
import MultiproofConePhysicalLevels
set_option autoImplicit false
namespace AspisR1.F3N_PhysicalRows
open Aeneas Aeneas.Std Result MultiproofConeRef
open F3N_PhysicalCode F3N_PhysicalNode

theorem rows (fuel : Nat) (s : reference.Scratch) (physical : Slice U8) (i w : Usize) :
    lower (Port9OR_P6Rows.rows fuel s physical i w)=
      MultiproofConePhysicalLevels.rows fuel s physical i w := by
  induction fuel generalizing s i w with
  | zero =>
    simp only [Port9OR_P6Rows.rows,MultiproofConePhysicalLevels.rows,conditional,lower,F3N_PhysicalNode.lift]
    split <;> rfl
  | succ fuel ih =>
    simp only [Port9OR_P6Rows.rows,MultiproofConePhysicalLevels.rows,conditional]
    split
    · rfl
    · rw [F3N_PhysicalBind.bind,F3N_PhysicalNode.node]
      unfold MultiproofConePhysicalLevels.bindRun
      congr 1
      funext r
      cases r with
      | fail e=>rfl
      | div=>rfl
      | ok out=>cases out with
        | Stop stopped=>rfl
        | Next after ni nw=>exact ih after ni nw

#print axioms rows
end AspisR1.F3N_PhysicalRows
