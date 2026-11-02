import PV_B3P_RawRows550227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Success227
set_option autoImplicit false

/-- The non-short-circuit source visits all four cells, even after false. -/
def debug_row550 (bound : U64) (row : Limbs64_550) : Result Bool := do
  let a ← Array.index_usize row 0#usize
  let b ← Array.index_usize row 1#usize
  let c ← Array.index_usize row 2#usize
  let d ← Array.index_usize row 3#usize
  .ok (((true && a < bound) && b < bound) && c < bound && d < bound)

def debug_matrix550 (bound : U64) (rows : Array Limbs64_550 4#usize) : Result Bool := do
  let values ← from_fn_four550 (fun i => do
    let row ← Array.index_usize rows i
    debug_row550 bound row)
  .ok (values.val.all id)

theorem debug_row_total550 (bound : U64) (row : Limbs64_550) :
    Success (debug_row550 bound row) := by
  unfold debug_row550
  apply bind _ _ (index row 0#usize (by decide))
  intro a
  apply bind _ _ (index row 1#usize (by decide))
  intro b
  apply bind _ _ (index row 2#usize (by decide))
  intro c
  apply bind _ _ (index row 3#usize (by decide))
  intro d
  exact ok _

theorem debug_matrix_total550 (bound : U64) (rows : Array Limbs64_550 4#usize) :
    Success (debug_matrix550 bound rows) := by
  unfold debug_matrix550
  apply bind
  · apply from_fn_four_total550
    intro i hi
    apply bind _ _ (index rows i hi)
    intro row
    exact debug_row_total550 bound row
  intro values
  exact ok _

theorem ignored_debug_matrix550 {α : Type} (bound : U64)
    (rows : Array Limbs64_550 4#usize) (next : Result α) :
    (do let _ ← debug_matrix550 bound rows; next) = next :=
  ignored_total_continuation550 _ (debug_matrix_total550 bound rows) next

#print axioms debug_row_total550
#print axioms debug_matrix_total550
#print axioms ignored_debug_matrix550
end PV_B3P_Association550227
