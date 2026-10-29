import PV_B3P_PreparedType14227
namespace PV_B3P_PreparedNative14227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding13227 PV_B3P_Binding12227
set_option autoImplicit false

def native_product_term14 (left : Array NativePrepared14 3#usize)
    (right : Array aspis_core.field.QM31 3#usize)
    (sums : PV_B3P_Binding9227.Matrix3x3) (index : Usize) :
    Result PV_B3P_Binding9227.Matrix3x3 := do
  let r ← Array.index_usize right index
  let l ← Array.index_usize left index
  source_accumulate13 sums r (to_reference14 l)

attribute [local irreducible] source_accumulate13 source_channel_reconstruct13

theorem native_product_term_binding14 (left : Array NativePrepared14 3#usize)
    (right : Array aspis_core.field.QM31 3#usize)
    (sums : PV_B3P_Binding9227.Matrix3x3) (index : Usize) :
    source_product_term13 (map_array14 to_reference14 left) right sums index =
      native_product_term14 left right sums index := by
  unfold source_product_term13 native_product_term14
  rw [map_array_index14]
  apply congrArg (Aeneas.Std.bind _)
  funext r
  rw [PV_B3P_Ordered227.bind_assoc]
  simp only [bind_tc_ok]

def native_prepared14 (left : Array NativePrepared14 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) : Result aspis_core.field.QM31 := do
  let initial := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
  let sums ← range_loop13 (native_product_term14 left right) 0#usize 3#usize initial
  source_channel_reconstruct13 sums

theorem native_prepared_binding14 (left : Array NativePrepared14 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) :
    native_prepared14 left right =
      reference_field.qm31_sum_products3_prepared (map_array14 to_reference14 left) right := by
  rw [← source_prepared_binding13]
  unfold native_prepared14 source_prepared13
  have steps : source_product_term13 (map_array14 to_reference14 left) right =
      native_product_term14 left right := by
    funext sums index
    exact native_product_term_binding14 left right sums index
  rw [steps]
#print axioms native_product_term_binding14
#print axioms native_prepared_binding14
end PV_B3P_PreparedNative14227
