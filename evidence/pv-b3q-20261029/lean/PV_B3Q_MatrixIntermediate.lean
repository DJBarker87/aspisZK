import PV_B3P_PreparedNative14227
import PV_B3Q_MatrixTrace
namespace PV_B3Q_MatrixIntermediate
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding13227 PV_B3P_Binding12227
  PV_B3P_PreparedNative14227 PV_B3P_Binding14227
set_option autoImplicit false
abbrev Matrix := PV_B3P_Binding9227.Matrix3x3
/-- Source loop observation immediately before reconstruction. It retains the
actual private payload's nine fields through the established fieldwise port. -/
def source_intermediate (left : Array NativePrepared14 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) : Result Matrix :=
 range_loop13 (native_product_term14 left right) 0#usize 3#usize
   (Array.repeat 3#usize (Array.repeat 3#usize 0#u64))
/-- Same observation in the emitted model: three complete accumulate results,
with no reconstruction that could conceal a wrong intermediate entry. -/
def emitted_intermediate (left : Array reference_field.PreparedQm31Multiplier 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) : Result Matrix :=
 PV_B3P_Binding9227.usize_plan (fun sums index => do
   let r ← Array.index_usize right index
   let l ← Array.index_usize left index
   reference_field.accumulate_prepared227 sums r l)
   3 0#usize (Array.repeat 3#usize (Array.repeat 3#usize 0#u64))
attribute [local irreducible] reference_field.accumulate_prepared227
  native_product_term14 Array.index_usize

theorem complete_matrix_binding (left : Array NativePrepared14 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) :
    source_intermediate left right = emitted_intermediate (map_array14 to_reference14 left) right := by
 unfold source_intermediate
 have terms : native_product_term14 left right =
     source_product_term13 (map_array14 to_reference14 left) right := by
   funext sums index
   exact (native_product_term_binding14 left right sums index).symm
 rw [terms,range_loop_binding13]
 unfold emitted_intermediate source_product_term13
 have accumulation : (fun sums r l => source_accumulate13 sums r l) =
     (fun sums r l => reference_field.accumulate_prepared227 sums r l) := by
   funext sums r l
   rw [source_accumulate_binding13]
   exact (accumulate_nested_binding12 sums r l).symm
 rw [accumulation]

/-- Observe all nine raw U64 entries; equality is before reconstruction. -/
theorem all_nine_binding (left : Array NativePrepared14 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) :
    (do let sums ← source_intermediate left right; .ok (PV_B3Q_Matrix.entries sums)) =
    (do let sums ← emitted_intermediate (map_array14 to_reference14 left) right
        .ok (PV_B3Q_Matrix.entries sums)) := by
 rw [complete_matrix_binding]
/-- The matrix observation and storage law hold together for the same port.
This is an instance of the existing link, never a replacement predicate. -/
theorem matrix_link_with_intermediate :
    PV_B3P_Link_matrix_stores PV_B3Q_Matrix.deployed_store ∧
    ∀ left right, source_intermediate left right =
      emitted_intermediate (map_array14 to_reference14 left) right :=
 ⟨PV_B3Q_Matrix.deployed_store_link,complete_matrix_binding⟩
#print axioms complete_matrix_binding
#print axioms all_nine_binding
#print axioms matrix_link_with_intermediate
end PV_B3Q_MatrixIntermediate
