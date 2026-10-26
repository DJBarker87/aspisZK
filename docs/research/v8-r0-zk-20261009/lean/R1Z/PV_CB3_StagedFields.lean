-- Closed subset of the retained named extracted canonical constructor.
import R1Z.ProverRwFullTypes
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedFields
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
abbrev aspis_core.field.M31 := ProverRwFull.aspis_core.field.M31
abbrev aspis_core.field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31
abbrev aspis_core.field.wide_exact.WideExact := ProverRwFull.aspis_core.field.wide_exact.WideExact
abbrev aspis_core.field.wide_exact.canonical_qm31.closure := Unit
abbrev aspis_core.field.P : Result U32 := .ok 2147483647#u32
def aspis_core.field.ct.subtract_p (x : Std.U32) : Result Std.U32 := do
  let i ← aspis_core.field.P
  let i1 ← lift (UScalar.cast_fromBool .U32 (x >= i))
  let mask ← lift (core.num.U32.wrapping_sub 0#u32 i1)
  let i2 ← lift (i &&& mask)
  ok (core.num.U32.wrapping_sub x i2)

def aspis_core.field.ct.reduce64 (x : Std.U64) : Result Std.U32 := do
  let i ← aspis_core.field.P
  let i1 ← lift (UScalar.cast .U64 i)
  let i2 ← lift (x &&& i1)
  let i3 ← lift (Std.U64.wrapping_shr x 31#u32)
  let x1 ← lift (Std.U64.wrapping_add i2 i3)
  let i4 ← lift (UScalar.cast .U64 i)
  let i5 ← lift (x1 &&& i4)
  let i6 ← lift (Std.U64.wrapping_shr x1 31#u32)
  let x2 ← lift (Std.U64.wrapping_add i5 i6)
  let i7 ← lift (UScalar.cast .U32 x2)
  aspis_core.field.ct.subtract_p i7

def
  aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
  (c : aspis_core.field.wide_exact.canonical_qm31.closure)
  (tupled_args : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let i ← lift (UScalar.cast .U64 tupled_args)
  let i1 ← aspis_core.field.ct.reduce64 i
  ok i1

def aspis_core.field.wide_exact.canonical_qm31
  (value : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let m ←
    aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
      () value.c0.a
  let m1 ←
    aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
      () value.c0.b
  let m2 ←
    aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
      () value.c1.a
  let m3 ←
    aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call
      () value.c1.b
  ok { c0 := { a := m, b := m1 }, c1 := { a := m2, b := m3 } }

def aspis_core.field.wide_exact.WideExact.new
  (c0 : aspis_core.field.QM31) (c1 : aspis_core.field.QM31) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  let q ← aspis_core.field.wide_exact.canonical_qm31 c0
  let q1 ← aspis_core.field.wide_exact.canonical_qm31 c1
  ok { c0 := q, c1 := q1 }


#print axioms aspis_core.field.wide_exact.WideExact.new
end R1Z.PV_CB3_StagedFields
