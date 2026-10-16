import EmptyRootExecution
import R0P.EmptyRoots
import ExtractedMaskTowerAdd

/-! The fixed data comparison is only21x8 native word literals. There is no
field recurrence or finite-field normalization; bounds are Nat comparisons. -/
set_option autoImplicit false
namespace AspisR1.EmptyRootTableFacts
open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe
abbrev table := AspisR1.EmptyRootExecution.table
abbrev P := AspisR1.ExtractedMaskTowerAdd.P

def tableCell (level : Fin 21) (lane : Fin 8) : U32 :=
  (table.val[level.val]'(by simpa [table.property] using level.isLt)).val[lane.val]'(by
    simpa using lane.isLt)

theorem table_values (level : Fin 21) (lane : Fin 8) :
    (tableCell level lane).val = R0P.emptyRootsNat level lane := by
  unfold tableCell table AspisR1.EmptyRootExecution.table
  unfold AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
    R0P.emptyRootsNat
  fin_cases level <;> fin_cases lane <;> rfl

theorem old_table_bound (level : Fin 21) (lane : Fin 8) :
    R0P.emptyRootsNat level lane < P := by
  fin_cases level <;> fin_cases lane <;>
    norm_num [R0P.emptyRootsNat, P, AspisR1.ExtractedMaskTowerAdd.P,
      AspisR1.ExtractedMaskM31AddSub.P]

theorem table_canonical (level : Fin 21) (lane : Fin 8) :
    (tableCell level lane).val < P := by
  rw [table_values]
  exact old_table_bound level lane

#print axioms table_values
#print axioms old_table_bound
#print axioms table_canonical
end AspisR1.EmptyRootTableFacts
