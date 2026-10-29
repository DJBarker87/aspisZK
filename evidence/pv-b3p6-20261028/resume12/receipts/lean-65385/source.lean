import PV_B3P_PreparedAccumulate12227
import PV_B3P_P227_01
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false

def source_product_term12 (left : Array reference_field.PreparedQm31Multiplier 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) (sums : Matrix3x3) (index : Usize) : Result Matrix3x3 := do
  let r ← Array.index_usize right index
  let l ← Array.index_usize left index
  source_accumulate12 sums r l

def source_channel_reconstruct12 (sums : Matrix3x3) : Result aspis_core.field.QM31 := do
  let a ← Array.index_usize sums 0#usize
  let m0 ← reference_field.reconstruct_component a
  let b ← Array.index_usize sums 1#usize
  let m1 ← reference_field.reconstruct_component b
  let c ← Array.index_usize sums 2#usize
  let m2 ← reference_field.reconstruct_component c
  let rotated ← reference_field.cm31_mul_r m1
  let c0 ← aspis_core.field.CM31.add m0 rotated
  let delta ← aspis_core.field.CM31.sub m2 m0
  let c1 ← aspis_core.field.CM31.sub delta m1
  .ok {c0:=c0,c1:=c1}

def source_prepared12 (left : Array reference_field.PreparedQm31Multiplier 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) : Result aspis_core.field.QM31 := do
  let initial := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)
  let sums ← loop (usize_body (source_product_term12 left right) 3#usize) (initial,0#usize)
  source_channel_reconstruct12 sums

attribute [local irreducible] Array.index_usize source_accumulate12
  reference_field.accumulate_prepared227 reference_field.reconstruct_component
  reference_field.cm31_mul_r aspis_core.field.CM31.add aspis_core.field.CM31.sub

theorem prepared_root_binding12 (left : Array reference_field.PreparedQm31Multiplier 3#usize)
    (right : Array aspis_core.field.QM31 3#usize) :
    reference_field.qm31_sum_products3_prepared left right = source_prepared12 left right := by
  unfold source_prepared12
  rw [three_loop12]
  simp only [reference_field.qm31_sum_products3_prepared,source_product_term12,
    source_channel_reconstruct12,accumulate_nested_binding12,PV_B3P_Ordered227.bind_assoc]

#print axioms prepared_root_binding12
end PV_B3P_Binding12227
