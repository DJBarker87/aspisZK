import R1Z.ProverRwP6FlatTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6BoundarySource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
abbrev aspis_core.field.M31.reduce_u64 := ProverRwSuccessNativePorts.aspis_core.field.ct.reduce64
abbrev aspis_core.field.CM31.new := ProverRwDictionaryBytes.Src.complex
structure BoundaryAcc where
  a : Std.U64
  b : Std.U64
  c : Std.U64
  d : Std.U64

/-- [prover_rw_success_p6::boundary_acc_step]:
    Source: 'lib.rs', lines 146:0-148:1
    Visibility: public -/
def boundary_acc_step
  (x : aspis_core.field.QM31) (s : BoundaryAcc) : Result BoundaryAcc := do
  let i := x.c0.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 ← lift (Std.U64.wrapping_add s.a i1)
  let i3 := x.c0.b
  let i4 ← lift (core.convert.num.FromU64U32.from i3)
  let i5 ← lift (Std.U64.wrapping_add s.b i4)
  let i6 := x.c1.a
  let i7 ← lift (core.convert.num.FromU64U32.from i6)
  let i8 ← lift (Std.U64.wrapping_add s.c i7)
  let i9 := x.c1.b
  let i10 ← lift (core.convert.num.FromU64U32.from i9)
  let i11 ← lift (Std.U64.wrapping_add s.d i10)
  ok { a := i2, b := i5, c := i8, d := i11 }

/-- [prover_rw_success_p6::boundary_flat]:
    Source: 'lib.rs', lines 176:0-207:1
    Visibility: public -/
def boundary_flat
  (p : Array aspis_core.field.QM31 28#usize) :
  Result aspis_core.field.QM31
  := do
  let x ← Array.index_usize p 0#usize
  let i := x.c0.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 ← lift (Std.U64.wrapping_mul 2#u64 i1)
  let i3 := x.c0.b
  let i4 ← lift (core.convert.num.FromU64U32.from i3)
  let i5 ← lift (Std.U64.wrapping_mul 2#u64 i4)
  let i6 := x.c1.a
  let i7 ← lift (core.convert.num.FromU64U32.from i6)
  let i8 ← lift (Std.U64.wrapping_mul 2#u64 i7)
  let i9 := x.c1.b
  let i10 ← lift (core.convert.num.FromU64U32.from i9)
  let i11 ← lift (Std.U64.wrapping_mul 2#u64 i10)
  let q ← Array.index_usize p 1#usize
  let s ← boundary_acc_step q { a := i2, b := i5, c := i8, d := i11 }
  let q1 ← Array.index_usize p 2#usize
  let s1 ← boundary_acc_step q1 s
  let q2 ← Array.index_usize p 3#usize
  let s2 ← boundary_acc_step q2 s1
  let q3 ← Array.index_usize p 4#usize
  let s3 ← boundary_acc_step q3 s2
  let q4 ← Array.index_usize p 5#usize
  let s4 ← boundary_acc_step q4 s3
  let q5 ← Array.index_usize p 6#usize
  let s5 ← boundary_acc_step q5 s4
  let q6 ← Array.index_usize p 7#usize
  let s6 ← boundary_acc_step q6 s5
  let q7 ← Array.index_usize p 8#usize
  let s7 ← boundary_acc_step q7 s6
  let q8 ← Array.index_usize p 9#usize
  let s8 ← boundary_acc_step q8 s7
  let q9 ← Array.index_usize p 10#usize
  let s9 ← boundary_acc_step q9 s8
  let q10 ← Array.index_usize p 11#usize
  let s10 ← boundary_acc_step q10 s9
  let q11 ← Array.index_usize p 12#usize
  let s11 ← boundary_acc_step q11 s10
  let q12 ← Array.index_usize p 13#usize
  let s12 ← boundary_acc_step q12 s11
  let q13 ← Array.index_usize p 14#usize
  let s13 ← boundary_acc_step q13 s12
  let q14 ← Array.index_usize p 15#usize
  let s14 ← boundary_acc_step q14 s13
  let q15 ← Array.index_usize p 16#usize
  let s15 ← boundary_acc_step q15 s14
  let q16 ← Array.index_usize p 17#usize
  let s16 ← boundary_acc_step q16 s15
  let q17 ← Array.index_usize p 18#usize
  let s17 ← boundary_acc_step q17 s16
  let q18 ← Array.index_usize p 19#usize
  let s18 ← boundary_acc_step q18 s17
  let q19 ← Array.index_usize p 20#usize
  let s19 ← boundary_acc_step q19 s18
  let q20 ← Array.index_usize p 21#usize
  let s20 ← boundary_acc_step q20 s19
  let q21 ← Array.index_usize p 22#usize
  let s21 ← boundary_acc_step q21 s20
  let q22 ← Array.index_usize p 23#usize
  let s22 ← boundary_acc_step q22 s21
  let q23 ← Array.index_usize p 24#usize
  let s23 ← boundary_acc_step q23 s22
  let q24 ← Array.index_usize p 25#usize
  let s24 ← boundary_acc_step q24 s23
  let q25 ← Array.index_usize p 26#usize
  let s25 ← boundary_acc_step q25 s24
  let q26 ← Array.index_usize p 27#usize
  let s26 ← boundary_acc_step q26 s25
  let m ← aspis_core.field.M31.reduce_u64 s26.a
  let m1 ← aspis_core.field.M31.reduce_u64 s26.b
  let c ← aspis_core.field.CM31.new m m1
  let m2 ← aspis_core.field.M31.reduce_u64 s26.c
  let m3 ← aspis_core.field.M31.reduce_u64 s26.d
  let c1 ← aspis_core.field.CM31.new m2 m3
  ok { c0 := c, c1 }

end R1Z.ProverRwP6BoundarySource
