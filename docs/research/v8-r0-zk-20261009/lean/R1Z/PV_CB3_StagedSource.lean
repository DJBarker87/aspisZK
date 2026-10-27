-- Generated staged reference bodies; cuts bound to named source definitions.
-- Compatibility fix: the generated shift literal 32#i32 is normalized to 32#u32
-- for this Aeneas standard library wrapping_shl interface; same shift count.
import R1Z.PV_CB3_StagedFields
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedSource
open Aeneas Aeneas.Std Result ControlFlow Error
abbrev aspis_core.field.M31 := ProverRwFull.aspis_core.field.M31
abbrev aspis_core.field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31
abbrev aspis_core.field.wide_exact.WideExact := ProverRwFull.aspis_core.field.wide_exact.WideExact
abbrev aspis_core.field.P := PV_CB3_StagedFields.aspis_core.field.P
abbrev aspis_core.field.wide_exact.WideExact.new := PV_CB3_StagedFields.aspis_core.field.wide_exact.WideExact.new
/-- [pv_cb3_source::staged_reference::words]:
    Source: '../kani-proof/reference_split.rs', lines 3:0-14:1
    Visibility: public -/
def staged_reference.words
  (block : Array Std.U8 32#usize) : Result (Array Std.U32 8#usize) := do
  let i ← Array.index_usize block 0#usize
  let i1 ← Array.index_usize block 1#usize
  let i2 ← Array.index_usize block 2#usize
  let i3 ← Array.index_usize block 3#usize
  let i4 ←
    lift (core.num.U32.from_le_bytes (Array.make 4#usize [ i, i1, i2, i3 ]))
  let i5 ← Array.index_usize block 4#usize
  let i6 ← Array.index_usize block 5#usize
  let i7 ← Array.index_usize block 6#usize
  let i8 ← Array.index_usize block 7#usize
  let i9 ←
    lift (core.num.U32.from_le_bytes (Array.make 4#usize [ i5, i6, i7, i8 ]))
  let i10 ← Array.index_usize block 8#usize
  let i11 ← Array.index_usize block 9#usize
  let i12 ← Array.index_usize block 10#usize
  let i13 ← Array.index_usize block 11#usize
  let i14 ←
    lift (core.num.U32.from_le_bytes
      (Array.make 4#usize [ i10, i11, i12, i13 ]))
  let i15 ← Array.index_usize block 12#usize
  let i16 ← Array.index_usize block 13#usize
  let i17 ← Array.index_usize block 14#usize
  let i18 ← Array.index_usize block 15#usize
  let i19 ←
    lift (core.num.U32.from_le_bytes
      (Array.make 4#usize [ i15, i16, i17, i18 ]))
  let i20 ← Array.index_usize block 16#usize
  let i21 ← Array.index_usize block 17#usize
  let i22 ← Array.index_usize block 18#usize
  let i23 ← Array.index_usize block 19#usize
  let i24 ←
    lift (core.num.U32.from_le_bytes
      (Array.make 4#usize [ i20, i21, i22, i23 ]))
  let i25 ← Array.index_usize block 20#usize
  let i26 ← Array.index_usize block 21#usize
  let i27 ← Array.index_usize block 22#usize
  let i28 ← Array.index_usize block 23#usize
  let i29 ←
    lift (core.num.U32.from_le_bytes
      (Array.make 4#usize [ i25, i26, i27, i28 ]))
  let i30 ← Array.index_usize block 24#usize
  let i31 ← Array.index_usize block 25#usize
  let i32 ← Array.index_usize block 26#usize
  let i33 ← Array.index_usize block 27#usize
  let i34 ←
    lift (core.num.U32.from_le_bytes
      (Array.make 4#usize [ i30, i31, i32, i33 ]))
  let i35 ← Array.index_usize block 28#usize
  let i36 ← Array.index_usize block 29#usize
  let i37 ← Array.index_usize block 30#usize
  let i38 ← Array.index_usize block 31#usize
  let i39 ←
    lift (core.num.U32.from_le_bytes
      (Array.make 4#usize [ i35, i36, i37, i38 ]))
  ok (Array.make 8#usize [ i4, i9, i14, i19, i24, i29, i34, i39 ])

/-- [pv_cb3_source::staged_reference::word_step]:
    Source: '../kani-proof/reference_split.rs', lines 15:0-18:1
    Visibility: public -/
def staged_reference.word_step
  (word : Std.U32) (remainder : Std.U64) : Result (Std.U32 × Std.U64) := do
  let i ← lift (Std.U64.wrapping_shl remainder 32#u32)
  let i1 ← lift (core.convert.num.FromU64U32.from word)
  let dividend ← lift (i ||| i1)
  let i2 ← aspis_core.field.P
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← dividend / i3
  let i5 ← lift (UScalar.cast .U32 i4)
  let i6 ← lift (core.convert.num.FromU64U32.from i2)
  let i7 ← dividend % i6
  ok (i5, i7)

/-- [pv_cb3_source::staged_reference::pass]:
    Source: '../kani-proof/reference_split.rs', lines 19:0-29:1
    Visibility: public -/
def staged_reference.pass
  (rank : Array Std.U32 8#usize) :
  Result ((Array Std.U32 8#usize) × Std.U32)
  := do
  let i ← Array.index_usize rank 7#usize
  let (q7, r1) ← staged_reference.word_step i 0#u64
  let i1 ← Array.index_usize rank 6#usize
  let (q6, r2) ← staged_reference.word_step i1 r1
  let i2 ← Array.index_usize rank 5#usize
  let (q5, r3) ← staged_reference.word_step i2 r2
  let i3 ← Array.index_usize rank 4#usize
  let (q4, r4) ← staged_reference.word_step i3 r3
  let i4 ← Array.index_usize rank 3#usize
  let (q3, r5) ← staged_reference.word_step i4 r4
  let i5 ← Array.index_usize rank 2#usize
  let (q2, r6) ← staged_reference.word_step i5 r5
  let i6 ← Array.index_usize rank 1#usize
  let (q1, r7) ← staged_reference.word_step i6 r6
  let i7 ← Array.index_usize rank 0#usize
  let (q0, r8) ← staged_reference.word_step i7 r7
  let i8 ← lift (UScalar.cast .U32 r8)
  ok (Array.make 8#usize [ q0, q1, q2, q3, q4, q5, q6, q7 ], i8)

/-- [pv_cb3_source::staged_reference::carry_step]:
    Source: '../kani-proof/reference_split.rs', lines 30:0-33:1
    Visibility: public -/
def staged_reference.carry_step
  (digit : Std.U32) (addend : Std.U32) : Result (Std.U32 × Std.U32) := do
  let i ← lift (core.convert.num.FromU64U32.from digit)
  let i1 ← lift (core.convert.num.FromU64U32.from addend)
  let sum ← lift (Std.U64.wrapping_add i i1)
  let i2 ← aspis_core.field.P
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← sum % i3
  let i5 ← lift (UScalar.cast .U32 i4)
  let i6 ← lift (core.convert.num.FromU64U32.from i2)
  let i7 ← sum / i6
  let i8 ← lift (UScalar.cast .U32 i7)
  ok (i5, i8)

/-- [pv_cb3_source::staged_reference::carry]:
    Source: '../kani-proof/reference_split.rs', lines 34:0-44:1
    Visibility: public -/
def staged_reference.carry
  (digits : Array Std.U32 8#usize) (addend : Std.U32) :
  Result ((Array Std.U32 8#usize) × Bool)
  := do
  let i ← Array.index_usize digits 0#usize
  let (d0, c1) ← staged_reference.carry_step i addend
  let i1 ← Array.index_usize digits 1#usize
  let (d1, c2) ← staged_reference.carry_step i1 c1
  let i2 ← Array.index_usize digits 2#usize
  let (d2, c3) ← staged_reference.carry_step i2 c2
  let i3 ← Array.index_usize digits 3#usize
  let (d3, c4) ← staged_reference.carry_step i3 c3
  let i4 ← Array.index_usize digits 4#usize
  let (d4, c5) ← staged_reference.carry_step i4 c4
  let i5 ← Array.index_usize digits 5#usize
  let (d5, c6) ← staged_reference.carry_step i5 c5
  let i6 ← Array.index_usize digits 6#usize
  let (d6, c7) ← staged_reference.carry_step i6 c6
  let i7 ← Array.index_usize digits 7#usize
  let (d7, c8) ← staged_reference.carry_step i7 c7
  ok (Array.make 8#usize [ d0, d1, d2, d3, d4, d5, d6, d7 ], c8 != 0#u32)

/-- [pv_cb3_source::staged_reference::gamma]:
    Source: '../kani-proof/reference_split.rs', lines 45:0-59:1
    Visibility: public -/
def staged_reference.gamma
  (block : Array Std.U8 32#usize) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  let rank0 ← staged_reference.words block
  let (rank1, d0) ← staged_reference.pass rank0
  let (rank2, d1) ← staged_reference.pass rank1
  let (rank3, d2) ← staged_reference.pass rank2
  let (rank4, d3) ← staged_reference.pass rank3
  let (rank5, d4) ← staged_reference.pass rank4
  let (rank6, d5) ← staged_reference.pass rank5
  let (rank7, d6) ← staged_reference.pass rank6
  let (rank8, d7) ← staged_reference.pass rank7
  let i ← Array.index_usize rank8 0#usize
  let i1 ← lift (Std.U32.wrapping_add i 1#u32)
  let (digits, wrapped) ←
    staged_reference.carry
      (Array.make 8#usize [ d0, d1, d2, d3, d4, d5, d6, d7 ]) i1
  let digits1 ←
    if wrapped
    then do
         let (digits2, _) ← staged_reference.carry digits 1#u32
         ok digits2
    else ok digits
  let i2 ← Array.index_usize digits1 0#usize
  let i3 ← Array.index_usize digits1 1#usize
  let i4 ← Array.index_usize digits1 2#usize
  let i5 ← Array.index_usize digits1 3#usize
  let i6 ← Array.index_usize digits1 4#usize
  let i7 ← Array.index_usize digits1 5#usize
  let i8 ← Array.index_usize digits1 6#usize
  let i9 ← Array.index_usize digits1 7#usize
  aspis_core.field.wide_exact.WideExact.new
    { c0 := { a := i2, b := i3 }, c1 := { a := i4, b := i5 } }
    { c0 := { a := i6, b := i7 }, c1 := { a := i8, b := i9 } }


#print axioms staged_reference.words
#print axioms staged_reference.word_step
#print axioms staged_reference.pass
#print axioms staged_reference.carry_step
#print axioms staged_reference.carry
#print axioms staged_reference.gamma
end R1Z.PV_CB3_StagedSource
