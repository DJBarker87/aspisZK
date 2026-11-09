import AspisR1SelectedMaskProbe.Funs
import AspisR1SelectedMaskProbe.Types
import ExtractedMaskPreparedState
import RPv_EqualityValueAdapter

/- Exact candidate 04fc field helper declarations: `qm31_sum_products3_prepared`
   and its three source loops (Funs.lean lines 378-480).  This isolated source
   owner does not replace the baseline generated Funs module. -/
set_option autoImplicit false
namespace AspisR1PoseidonPreparedSum3Source
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

def field.qm31_from_karatsuba_channel_sums.closure := Unit

/-- [aspis_r1_mask_extraction_probe::field::qm31_from_karatsuba_channel_sums::{impl core::ops::function::Fn<([u64; 3usize],), aspis_r1_mask_extraction_probe::field::CM31> for aspis_r1_mask_extraction_probe::field::qm31_from_karatsuba_channel_sums::closure}::call]:
    Source: 'src/field.rs', lines 482:22-490:5 -/
def
  field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
  (c : field.qm31_from_karatsuba_channel_sums.closure)
  (tupled_args : Array Std.U64 3#usize) :
  Result field.CM31
  := do
  let i ← Array.index_usize tupled_args 0#usize
  let m0 ← field.M31.reduce_u64 i
  let i1 ← Array.index_usize tupled_args 1#usize
  let m1 ← field.M31.reduce_u64 i1
  let i2 ← Array.index_usize tupled_args 2#usize
  let m2 ← field.M31.reduce_u64 i2
  let m ← field.M31.sub m0 m1
  let m3 ← field.M31.sub m2 m0
  let m4 ← field.M31.sub m3 m1
  ok { a := m, b := m4 }

/-- [aspis_r1_mask_extraction_probe::field::qm31_from_karatsuba_channel_sums]:
    Source: 'src/field.rs', lines 481:0-498:1 -/
def field.qm31_from_karatsuba_channel_sums
  (sums : Array (Array Std.U64 3#usize) 3#usize) : Result field.QM31 := do
  let a ← Array.index_usize sums 0#usize
  let m0 ←
    field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
      () a
  let a1 ← Array.index_usize sums 1#usize
  let m1 ←
    field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
      () a1
  let a2 ← Array.index_usize sums 2#usize
  let m2 ←
    field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
      () a2
  let c ← field.mul_by_r m1
  let c1 ← field.CM31.add m0 c
  let c2 ← field.CM31.sub m2 m0
  let c3 ← field.CM31.sub c2 m1
  ok { c0 := c1, c1 := c3 }

/-- [aspis_r1_mask_extraction_probe::field::qm31_sum_products3_prepared]: loop 2:
    Source: 'src/field.rs', lines 696:12-699:13
    Visibility: public -/
@[rust_loop]
def field.qm31_sum_products3_prepared_loop0_loop0_loop0
  (iter : core.ops.range.Range Std.Usize)
  (left : Array field.PreparedQm31Multiplier 3#usize)
  (sums : Array (Array Std.U64 3#usize) 3#usize) (index : Std.Usize)
  (right_components : Array (Array field.M31 3#usize) 3#usize)
  (component : Std.Usize) :
  Result (Array (Array Std.U64 3#usize) 3#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok sums
  | some channel =>
    let pqm ← Array.index_usize left index
    let a ← Array.index_usize pqm.components component
    let m ← Array.index_usize a channel
    let i ← lift (UScalar.cast .U64 m)
    let a1 ← Array.index_usize right_components component
    let m1 ← Array.index_usize a1 channel
    let i1 ← lift (UScalar.cast .U64 m1)
    let i2 ← i * i1
    let a2 ← Array.index_usize sums component
    let i3 ← Array.index_usize a2 channel
    let i4 ← i3 + i2
    let (a3, index_mut_back) ← Array.index_mut_usize sums component
    let a4 ← Array.update a3 channel i4
    let a5 := index_mut_back a4
    field.qm31_sum_products3_prepared_loop0_loop0_loop0 iter1 left a5 index
      right_components component
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::field::qm31_sum_products3_prepared]: loop 1:
    Source: 'src/field.rs', lines 695:8-700:9
    Visibility: public -/
@[rust_loop]
def field.qm31_sum_products3_prepared_loop0_loop0
  (iter : core.ops.range.Range Std.Usize)
  (left : Array field.PreparedQm31Multiplier 3#usize)
  (sums : Array (Array Std.U64 3#usize) 3#usize) (index : Std.Usize)
  (right_components : Array (Array field.M31 3#usize) 3#usize) :
  Result (Array (Array Std.U64 3#usize) 3#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok sums
  | some component =>
    let sums1 ←
      field.qm31_sum_products3_prepared_loop0_loop0_loop0
        { start := 0#usize, «end» := 3#usize } left sums index
        right_components component
    field.qm31_sum_products3_prepared_loop0_loop0 iter1 left sums1 index
      right_components
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::field::qm31_sum_products3_prepared]: loop 0:
    Source: 'src/field.rs', lines 680:4-701:5
    Visibility: public -/
@[rust_loop]
def field.qm31_sum_products3_prepared_loop0
  (iter : core.ops.range.Range Std.Usize)
  (left : Array field.PreparedQm31Multiplier 3#usize)
  (right : Array field.QM31 3#usize)
  (sums : Array (Array Std.U64 3#usize) 3#usize) :
  Result (Array (Array Std.U64 3#usize) 3#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok sums
  | some index =>
    let q ← Array.index_usize right index
    let right_sum ← field.CM31.add q.c0 q.c1
    let m ← field.M31.add q.c0.a q.c0.b
    let m1 ← field.M31.add q.c1.a q.c1.b
    let m2 ← field.M31.add right_sum.a right_sum.b
    let sums1 ←
      field.qm31_sum_products3_prepared_loop0_loop0
        { start := 0#usize, «end» := 3#usize } left sums index
        (Array.make 3#usize [
          Array.make 3#usize [ q.c0.a, q.c0.b, m ],
          Array.make 3#usize [ q.c1.a, q.c1.b, m1 ],
          Array.make 3#usize [ right_sum.a, right_sum.b, m2 ]
          ])
    field.qm31_sum_products3_prepared_loop0 iter1 left right sums1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::field::qm31_sum_products3_prepared]:
    Source: 'src/field.rs', lines 678:0-703:1
    Visibility: public -/
def field.qm31_sum_products3_prepared
  (left : Array field.PreparedQm31Multiplier 3#usize)
  (right : Array field.QM31 3#usize) :
  Result field.QM31
  := do
  let a := Array.repeat 3#usize 0#u64
  let sums := Array.repeat 3#usize a
  let sums1 ←
    field.qm31_sum_products3_prepared_loop0
      { start := 0#usize, «end» := 3#usize } left right sums
  field.qm31_from_karatsuba_channel_sums sums1

end AspisR1PoseidonPreparedSum3Source
