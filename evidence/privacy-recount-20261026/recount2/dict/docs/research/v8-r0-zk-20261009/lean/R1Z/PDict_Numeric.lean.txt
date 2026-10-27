import R1Z.PDict_Typenum
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Numeric
open Aeneas Aeneas.Std Result ProverRwFull

def op141 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result Isize := do
  let digit ← b.to_u8
  let upper ← u.to_isize
  let shifted ← Aeneas.Std.lift (Isize.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.hcast .Isize digit) ||| shifted)

def op142 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result I64 := do
  let digit ← b.to_u8
  let upper ← u.to_i64
  let shifted ← Aeneas.Std.lift (I64.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.hcast .I64 digit) ||| shifted)

def op143 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result I32 := do
  let digit ← b.to_u8
  let upper ← u.to_i32
  let shifted ← Aeneas.Std.lift (I32.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.hcast .I32 digit) ||| shifted)

def op144 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result I16 := do
  let digit ← b.to_u8
  let upper ← u.to_i16
  let shifted ← Aeneas.Std.lift (I16.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.hcast .I16 digit) ||| shifted)

def op145 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result I8 := do
  let digit ← b.to_u8
  let upper ← u.to_i8
  let shifted ← Aeneas.Std.lift (I8.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.hcast .I8 digit) ||| shifted)

def op146 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result Usize := do
  let digit ← b.to_u8
  let upper ← u.to_usize
  let shifted ← Aeneas.Std.lift (Usize.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.cast .Usize digit) ||| shifted)

def op147 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result U64 := do
  let digit ← b.to_u8
  let upper ← u.to_u64
  let shifted ← Aeneas.Std.lift (U64.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.cast .U64 digit) ||| shifted)

def op148 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result U32 := do
  let digit ← b.to_u8
  let upper ← u.to_u32
  let shifted ← Aeneas.Std.lift (U32.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.cast .U32 digit) ||| shifted)

def op149 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result U16 := do
  let digit ← b.to_u8
  let upper ← u.to_u16
  let shifted ← Aeneas.Std.lift (U16.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.cast .U16 digit) ||| shifted)

def op150 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result U8 := do
  let digit ← b.to_u8
  let upper ← u.to_u8
  let shifted ← Aeneas.Std.lift (U8.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.cast .U8 digit) ||| shifted)

def op151 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result Isize := do
  let digit ← b.U8
  let upper ← u.ISIZE
  let shifted ← Aeneas.Std.lift (Isize.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.hcast .Isize digit) ||| shifted)

def op152 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result I64 := do
  let digit ← b.U8
  let upper ← u.I64
  let shifted ← Aeneas.Std.lift (I64.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.hcast .I64 digit) ||| shifted)

def op153 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result I32 := do
  let digit ← b.U8
  let upper ← u.I32
  let shifted ← Aeneas.Std.lift (I32.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.hcast .I32 digit) ||| shifted)

def op154 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result I16 := do
  let digit ← b.U8
  let upper ← u.I16
  let shifted ← Aeneas.Std.lift (I16.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.hcast .I16 digit) ||| shifted)

def op155 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result I8 := do
  let digit ← b.U8
  let upper ← u.I8
  let shifted ← Aeneas.Std.lift (I8.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.hcast .I8 digit) ||| shifted)

def op156 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result Usize := do
  let digit ← b.U8
  let upper ← u.USIZE
  let shifted ← Aeneas.Std.lift (Usize.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.cast .Usize digit) ||| shifted)

def op157 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result U64 := do
  let digit ← b.U8
  let upper ← u.U64
  let shifted ← Aeneas.Std.lift (U64.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.cast .U64 digit) ||| shifted)

def op158 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result U32 := do
  let digit ← b.U8
  let upper ← u.U32
  let shifted ← Aeneas.Std.lift (U32.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.cast .U32 digit) ||| shifted)

def op159 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result U16 := do
  let digit ← b.U8
  let upper ← u.U16
  let shifted ← Aeneas.Std.lift (U16.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.cast .U16 digit) ||| shifted)

def op160 {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) : Result U8 := do
  let digit ← b.U8
  let upper ← u.U8
  let shifted ← Aeneas.Std.lift (U8.wrapping_shl upper 1#u32)
  Aeneas.Std.lift ((UScalar.cast .U8 digit) ||| shifted)

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  { PDict_Typenum.selected ops with
    op141 := @op141,
    op142 := @op142,
    op143 := @op143,
    op144 := @op144,
    op145 := @op145,
    op146 := @op146,
    op147 := @op147,
    op148 := @op148,
    op149 := @op149,
    op150 := @op150,
    op151 := @op151,
    op152 := @op152,
    op153 := @op153,
    op154 := @op154,
    op155 := @op155,
    op156 := @op156,
    op157 := @op157,
    op158 := @op158,
    op159 := @op159,
    op160 := @op160 }

theorem op141_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op141 u b = op141 u b := rfl

#print axioms op141_installed

theorem op142_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op142 u b = op142 u b := rfl

#print axioms op142_installed

theorem op143_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op143 u b = op143 u b := rfl

#print axioms op143_installed

theorem op144_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op144 u b = op144 u b := rfl

#print axioms op144_installed

theorem op145_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op145 u b = op145 u b := rfl

#print axioms op145_installed

theorem op146_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op146 u b = op146 u b := rfl

#print axioms op146_installed

theorem op147_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op147 u b = op147 u b := rfl

#print axioms op147_installed

theorem op148_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op148 u b = op148 u b := rfl

#print axioms op148_installed

theorem op149_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op149 u b = op149 u b := rfl

#print axioms op149_installed

theorem op150_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op150 u b = op150 u b := rfl

#print axioms op150_installed

theorem op151_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op151 u b = op151 u b := rfl

#print axioms op151_installed

theorem op152_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op152 u b = op152 u b := rfl

#print axioms op152_installed

theorem op153_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op153 u b = op153 u b := rfl

#print axioms op153_installed

theorem op154_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op154 u b = op154 u b := rfl

#print axioms op154_installed

theorem op155_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op155 u b = op155 u b := rfl

#print axioms op155_installed

theorem op156_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op156 u b = op156 u b := rfl

#print axioms op156_installed

theorem op157_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op157 u b = op157 u b := rfl

#print axioms op157_installed

theorem op158_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op158 u b = op158 u b := rfl

#print axioms op158_installed

theorem op159_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op159 u b = op159 u b := rfl

#print axioms op159_installed

theorem op160_installed (ops : ExternalFuns) {U B : Type}
    (u : typenum.marker_traits.Unsigned U) (b : typenum.marker_traits.Bit B) :
    (selected ops).op160 u b = op160 u b := rfl

#print axioms op160_installed

theorem bit_failure {U B : Type} (u : typenum.marker_traits.Unsigned U)
    (b : typenum.marker_traits.Bit B) (e : Error) (h : b.to_u8 = .fail e) :
    op150 u b = .fail e := by
  simp only [op150,h,bind_tc_fail]

#print axioms bit_failure
end R1Z.PDict_Numeric
