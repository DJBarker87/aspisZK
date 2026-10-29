import PV_B3P_RangeBinding13227
import PV_B3P_ClosureDrop13227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding12227 Result
set_option autoImplicit false

def source_component13 (left right : Channels12) (component : Usize) (sums : Matrix3x3) : Result Matrix3x3 :=
  range_loop13 (source_channel12 left right component) 0#usize 3#usize sums

theorem source_component_binding13 (left right : Channels12) (component : Usize) (sums : Matrix3x3) :
    source_component13 left right component sums = source_component12 left right component sums :=
  range_loop_binding13 _ _ _ _

def source_nested13 (left right : Channels12) (sums : Matrix3x3) : Result Matrix3x3 :=
  range_loop13 (fun sums component => source_component13 left right component sums) 0#usize 3#usize sums

theorem source_nested_binding13 (left right : Channels12) (sums : Matrix3x3) :
    source_nested13 left right sums = source_nested12 left right sums := by
  unfold source_nested13
  rw [range_loop_binding13]
  have steps : (fun sums component => source_component13 left right component sums) =
      (fun sums component => source_component12 left right component sums) := by
    funext sums component
    exact source_component_binding13 left right component sums
  rw [steps]
  rfl

def source_accumulate13 (sums : Matrix3x3) (right : aspis_core.field.QM31)
    (left : reference_field.PreparedQm31Multiplier) : Result Matrix3x3 := do
  let right_sum ← aspis_core.field.CM31.add right.c0 right.c1
  let m ← aspis_core.field.M31.add right.c0.a right.c0.b
  let m1 ← aspis_core.field.M31.add right.c1.a right.c1.b
  let m2 ← aspis_core.field.M31.add right_sum.a right_sum.b
  let channels := Array.make 3#usize [
    Array.make 3#usize [right.c0.a,right.c0.b,m] (by simp),
    Array.make 3#usize [right.c1.a,right.c1.b,m1] (by simp),
    Array.make 3#usize [right_sum.a,right_sum.b,m2] (by simp)] (by simp)
  source_nested13 left.components channels sums

def source_product_term13 (left : Array reference_field.PreparedQm31Multiplier 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) (sums : Matrix3x3) (index : Usize) : Result Matrix3x3 := do
  let r ← Array.index_usize right index
  let l ← Array.index_usize left index
  source_accumulate13 sums r l

def source_channel_reconstruct13 (sums : Matrix3x3) : Result aspis_core.field.QM31 := do
  let a ← Array.index_usize sums 0#usize
  let m0 ← reconstruct_call_once13 a
  let b ← Array.index_usize sums 1#usize
  let m1 ← reconstruct_call_once13 b
  let c ← Array.index_usize sums 2#usize
  let m2 ← reconstruct_call_once13 c
  let rotated ← reference_field.cm31_mul_r m1
  let c0 ← aspis_core.field.CM31.add m0 rotated
  let delta ← aspis_core.field.CM31.sub m2 m0
  let c1 ← aspis_core.field.CM31.sub delta m1
  .ok {c0:=c0,c1:=c1}

attribute [local irreducible] aspis_core.field.CM31.add aspis_core.field.M31.add
  reference_field.reconstruct_component reference_field.cm31_mul_r
  aspis_core.field.CM31.sub Array.index_usize

theorem source_accumulate_binding13 (sums : Matrix3x3) (right : aspis_core.field.QM31)
    (left : reference_field.PreparedQm31Multiplier) :
    source_accumulate13 sums right left = source_accumulate12 sums right left := by
  unfold source_accumulate13 source_accumulate12
  simp only [source_nested_binding13]

theorem source_product_term_binding13 (left : Array reference_field.PreparedQm31Multiplier 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) (sums : Matrix3x3) (index : Usize) :
    source_product_term13 left right sums index = source_product_term12 left right sums index := by
  unfold source_product_term13 source_product_term12
  simp only [source_accumulate_binding13]

theorem source_channel_reconstruct_binding13 (sums : Matrix3x3) :
    source_channel_reconstruct13 sums = source_channel_reconstruct12 sums := by
  unfold source_channel_reconstruct13 source_channel_reconstruct12
  simp only [reconstruct_call_once_binding13]

def source_prepared13 (left : Array reference_field.PreparedQm31Multiplier 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) : Result aspis_core.field.QM31 := do
  let initial := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
  let sums ← range_loop13 (source_product_term13 left right) 0#usize 3#usize initial
  source_channel_reconstruct13 sums

theorem source_prepared_binding13 (left : Array reference_field.PreparedQm31Multiplier 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) :
    source_prepared13 left right = reference_field.qm31_sum_products3_prepared left right := by
  rw [prepared_root_binding12]
  unfold source_prepared13 source_prepared12
  dsimp only
  rw [range_loop_binding13]
  have steps : source_product_term13 left right = source_product_term12 left right := by
    funext sums index
    exact source_product_term_binding13 left right sums index
  simp only [steps,source_channel_reconstruct_binding13]

theorem prepared_link13 :
    PV_B3P_Links13227.PV_B3P_Link_field_qm31_sum_products3_prepared source_prepared13 :=
  funext (fun left => funext (source_prepared_binding13 left))
#print axioms source_component_binding13
#print axioms source_nested_binding13
#print axioms source_accumulate_binding13
#print axioms source_product_term_binding13
#print axioms source_channel_reconstruct_binding13
#print axioms source_prepared_binding13
#print axioms prepared_link13
end PV_B3P_Binding13227
