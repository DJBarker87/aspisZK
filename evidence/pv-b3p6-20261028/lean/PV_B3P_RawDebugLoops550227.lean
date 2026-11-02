import PV_B3P_RawDebug550227
import PV_B3P_RangeFold13227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Success227 PV_B3P_Binding13227 PV_B3P_Binding11227
set_option autoImplicit false

theorem four_indices550 : usize_indices11 4 0#usize =
    [0#usize,1#usize,2#usize,3#usize] := by
  simp only [usize_indices11,next11_20_0,next11_20_1,next11_20_2,next11_20_3]

theorem range_four_total550 {α : Type} (step : α → Usize → Result α)
    (state : α) (total : ∀ s i, i.val < 4 → Success (step s i)) :
    Success (range_loop13 step 0#usize 4#usize state) := by
  rw [range_as_fold13 step 0#usize 4#usize 4 state (by rfl),four_indices550]
  simp only [PV_B3P_Ordered227.fold]
  apply bind _ _ (total state 0#usize (by decide))
  intro s1
  apply bind _ _ (total s1 1#usize (by decide))
  intro s2
  apply bind _ _ (total s2 2#usize (by decide))
  intro s3
  apply bind _ _ (total s3 3#usize (by decide))
  intro s4
  exact ok s4

def source_debug_row550 (bound : U64) (row : Limbs64_550) (flag : Bool) : Result Bool :=
  range_loop13 (fun flag limb => do
    let value ← Array.index_usize row limb
    .ok (flag && decide (value < bound))) 0#usize 4#usize flag

def source_debug_matrix550 (bound : U64) (rows : Array Limbs64_550 4#usize) : Result Bool :=
  range_loop13 (fun flag output => do
    let row ← Array.index_usize rows output
    source_debug_row550 bound row flag) 0#usize 4#usize true

theorem source_debug_row_total550 (bound : U64) (row : Limbs64_550) (flag : Bool) :
    Success (source_debug_row550 bound row flag) := by
  apply range_four_total550
  intro flag limb hl
  apply bind _ _ (index row limb hl)
  intro value
  exact ok _

theorem source_debug_matrix_total550 (bound : U64) (rows : Array Limbs64_550 4#usize) :
    Success (source_debug_matrix550 bound rows) := by
  apply range_four_total550
  intro flag output ho
  apply bind _ _ (index rows output ho)
  intro row
  exact source_debug_row_total550 bound row flag

theorem ignored_source_debug_loops550 {α : Type} (bound : U64)
    (rows : Array Limbs64_550 4#usize) (next : Result α) :
    (do let _ ← source_debug_matrix550 bound rows; next) = next :=
  ignored_total_continuation550 _ (source_debug_matrix_total550 bound rows) next

#print axioms four_indices550
#print axioms range_four_total550
#print axioms source_debug_row_total550
#print axioms source_debug_matrix_total550
#print axioms ignored_source_debug_loops550
end PV_B3P_Association550227
