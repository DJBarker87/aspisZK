import PV_B3P_NineUnroll9227
import PV_B3P_P227_12
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Ordered227
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31

def equality_step (left right : Array Q 10#usize) (product : Q) (i : Usize) : Result Q := do
  let l ← Array.index_usize left i
  let r ← Array.index_usize right i
  let factor ← reference_terminal.equality_factor l r
  aspis_core.field.QM31.mul product factor

/-- The deployed source's increasing while loop, including its original guard. -/
def source_equality_loop (left right : Array Q 10#usize) (product : Q) (i : Usize) : Result Q :=
  loop (usize_body (equality_step left right) 10#usize) (product,i)

def source_equality_value (left right : Array Q 10#usize) : Result Q := do
  let l ← Array.index_usize left 0#usize
  let r ← Array.index_usize right 0#usize
  let product ← reference_terminal.equality_factor l r
  source_equality_loop left right product 1#usize

attribute [local irreducible] aspis_core.field.QM31.mul reference_terminal.equality_factor
  Array.index_usize

theorem equality_loop_binding (left right : Array Q 10#usize) (product : Q) :
    source_equality_loop left right product 1#usize =
      usize_plan (equality_step left right) 9 1#usize product :=
  usize_loop_plan (equality_step left right) 10#usize 1#usize 9 product rfl

/-- Structural normalization only: ten opaque factors and nine opaque products. -/
theorem equality_entry_factor (left right : Array Q 10#usize) :
    reference_terminal.equality_value left right = (do
      let l ← Array.index_usize left 0#usize
      let r ← Array.index_usize right 0#usize
      let product ← reference_terminal.equality_factor l r
      usize_plan (equality_step left right) 9 1#usize product) := by
  simp only [forward_nine,equality_step,bind_assoc,reference_terminal.equality_value]

theorem equality_body_binding (left right : Array Q 10#usize) :
    source_equality_value left right = reference_terminal.equality_value left right := by
  unfold source_equality_value
  simp only [equality_loop_binding]
  exact (equality_entry_factor left right).symm

#print axioms equality_loop_binding
#print axioms equality_entry_factor
#print axioms equality_body_binding
end PV_B3P_Binding9227
