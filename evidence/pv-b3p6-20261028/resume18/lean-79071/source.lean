import PV_B3P_DigestCpsEq9227
import PV_B3P_P227_01
namespace PV_B3P_Association554227
open Aeneas Aeneas.Std PV_B3P_227 Result PV_B3P_Binding9227
set_option autoImplicit false
abbrev DotRaw554 := Array U64 4#usize

def dot_cell554 (weights : Array aspis_core.field.QM31 7#usize)
    (values : Array aspis_core.field.M31 7#usize) (index : Usize)
    (raw : DotRaw554) : Result DotRaw554 := do
  let m ← Array.index_usize values index
  let value ← lift (UScalar.cast .U64 m)
  let weight ← Array.index_usize weights index
  let limb0 ← lift (UScalar.cast .U64 weight.c0.a)
  let product0 ← lift (U64.wrapping_mul limb0 value)
  let old0 ← Array.index_usize raw 0#usize
  let next0 ← lift (U64.wrapping_add old0 product0)
  let raw1 ← Array.update raw 0#usize next0
  let limb1 ← lift (UScalar.cast .U64 weight.c0.b)
  let product1 ← lift (U64.wrapping_mul limb1 value)
  let old1 ← Array.index_usize raw1 1#usize
  let next1 ← lift (U64.wrapping_add old1 product1)
  let raw2 ← Array.update raw1 1#usize next1
  let limb2 ← lift (UScalar.cast .U64 weight.c1.a)
  let product2 ← lift (U64.wrapping_mul limb2 value)
  let old2 ← Array.index_usize raw2 2#usize
  let next2 ← lift (U64.wrapping_add old2 product2)
  let raw3 ← Array.update raw2 2#usize next2
  let limb3 ← lift (UScalar.cast .U64 weight.c1.b)
  let product3 ← lift (U64.wrapping_mul limb3 value)
  let old3 ← Array.index_usize raw3 3#usize
  let next3 ← lift (U64.wrapping_add old3 product3)
  let raw4 ← Array.update raw3 3#usize next3
  .ok raw4

def dot_reduce554 (raw sums : DotRaw554) : Result DotRaw554 := do
  let r0 ← Array.index_usize raw 0#usize
  let m0 ← aspis_core.field.M31.reduce_u64 r0
  let value0 ← lift (UScalar.cast .U64 m0)
  let old0 ← Array.index_usize sums 0#usize
  let next0 ← lift (U64.wrapping_add old0 value0)
  let sums1 ← Array.update sums 0#usize next0
  let r1 ← Array.index_usize raw 1#usize
  let m1 ← aspis_core.field.M31.reduce_u64 r1
  let value1 ← lift (UScalar.cast .U64 m1)
  let old1 ← Array.index_usize sums1 1#usize
  let next1 ← lift (U64.wrapping_add old1 value1)
  let sums2 ← Array.update sums1 1#usize next1
  let r2 ← Array.index_usize raw 2#usize
  let m2 ← aspis_core.field.M31.reduce_u64 r2
  let value2 ← lift (UScalar.cast .U64 m2)
  let old2 ← Array.index_usize sums2 2#usize
  let next2 ← lift (U64.wrapping_add old2 value2)
  let sums3 ← Array.update sums2 2#usize next2
  let r3 ← Array.index_usize raw 3#usize
  let m3 ← aspis_core.field.M31.reduce_u64 r3
  let value3 ← lift (UScalar.cast .U64 m3)
  let old3 ← Array.index_usize sums3 3#usize
  let next3 ← lift (U64.wrapping_add old3 value3)
  let sums4 ← Array.update sums3 3#usize next3
  .ok sums4

def dot_finish554 (sums : DotRaw554) : Result aspis_core.field.QM31 := do
  let r0 ← Array.index_usize sums 0#usize
  let m0 ← aspis_core.field.M31.reduce_u64 r0
  let r1 ← Array.index_usize sums 1#usize
  let m1 ← aspis_core.field.M31.reduce_u64 r1
  let c0 ← aspis_core.field.CM31.new m0 m1
  let r2 ← Array.index_usize sums 2#usize
  let m2 ← aspis_core.field.M31.reduce_u64 r2
  let r3 ← Array.index_usize sums 3#usize
  let m3 ← aspis_core.field.M31.reduce_u64 r3
  let c1 ← aspis_core.field.CM31.new m2 m3
  .ok { c0, c1 }

def dot_source554 (weights : Array aspis_core.field.QM31 7#usize)
    (values : Array aspis_core.field.M31 7#usize) : Result aspis_core.field.QM31 := do
  let sums := Array.repeat 4#usize 0#u64
  let raw := Array.repeat 4#usize 0#u64
  let raw1 ← dot_cell554 weights values 0#usize raw
  let raw2 ← dot_cell554 weights values 1#usize raw1
  let raw3 ← dot_cell554 weights values 2#usize raw2
  let raw4 ← dot_cell554 weights values 3#usize raw3
  let sums1 ← dot_reduce554 raw4 sums
  let rawNext := Array.repeat 4#usize 0#u64
  let rawNext1 ← dot_cell554 weights values 4#usize rawNext
  let rawNext2 ← dot_cell554 weights values 5#usize rawNext1
  let rawNext3 ← dot_cell554 weights values 6#usize rawNext2
  let sums2 ← dot_reduce554 rawNext3 sums1
  dot_finish554 sums2

#print axioms dot_source554
end PV_B3P_Association554227
