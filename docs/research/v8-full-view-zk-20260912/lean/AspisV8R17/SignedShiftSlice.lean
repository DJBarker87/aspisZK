import AspisV8R17.UnsignedReducerOps
import Mathlib.Data.Int.Notation

/-! Minimal signed-count runtime projection. The toNat automation attributes
are deliberately not imported; its declaration body is retained. Literal
construction and the generated M31.half caller are separate obligations. -/
namespace Aeneas.Std
open Result Error

-- SOURCE Core.lean
inductive IScalarTy where
| Isize
| I8
| I16
| I32
| I64
| I128
deriving BvEnumToBitVec
-- END SOURCE

-- SOURCE Core.lean
@[implicit_reducible]
def IScalarTy.numBits (ty : IScalarTy) : Nat :=
  match ty with
  | Isize => System.Platform.numBits
  | I8 => 8
  | I16 => 16
  | I32 => 32
  | I64 => 64
  | I128 => 128
-- END SOURCE

-- SOURCE Core.lean
structure IScalar (ty : IScalarTy) where
  /- The internal representation is a bit-vector -/
  bv : BitVec ty.numBits
deriving Repr, BEq, DecidableEq
-- END SOURCE

-- SOURCE Core.lean
def IScalar.val {ty} (x : IScalar ty) : ℤ := x.bv.toInt
-- END SOURCE

-- SOURCE Core.lean
abbrev IScalar.toNat {ty} (x : IScalar ty) : Nat := x.val.toNat
-- END SOURCE

-- SOURCE Bitwise.lean
def UScalar.shiftLeft {ty : UScalarTy} (x : UScalar ty) (s : Nat) :
  Result (UScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.bv.shiftLeft s ⟩
  else fail .integerOverflow
-- END SOURCE

-- SOURCE Bitwise.lean
def UScalar.shiftLeft_IScalar {ty tys} (x : UScalar ty) (s : IScalar tys) :
  Result (UScalar ty) :=
  if s.val ≥ 0 then
    x.shiftLeft s.toNat
  else fail .integerOverflow
-- END SOURCE

-- SOURCE Bitwise.lean
def UScalar.shiftRight_IScalar {ty tys} (x : UScalar ty) (s : IScalar tys) :
  Result (UScalar ty) :=
  if s.val ≥ 0 then
    x.shiftRight s.toNat
  else fail .integerOverflow
-- END SOURCE

-- SOURCE Bitwise.lean
def UScalar.or {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv ||| y.bv ⟩
-- END SOURCE
end Aeneas.Std

namespace AspisV8R17.SignedShiftSlice
open Aeneas.Std

theorem right_success {ty tys} (x : UScalar ty) (s : IScalar tys)
    (h0 : 0 ≤ s.val) (hs : s.toNat < ty.numBits) :
    ∃ z, UScalar.shiftRight_IScalar x s = .ok z ∧
      z.val = x.val >>> s.toNat := by
  simpa only [UScalar.shiftRight_IScalar, h0, if_pos] using
    UnsignedReducerOps.shift_success x s.toNat hs

theorem left_success {ty tys} (x : UScalar ty) (s : IScalar tys)
    (h0 : 0 ≤ s.val) (hs : s.toNat < ty.numBits) :
    ∃ z, UScalar.shiftLeft_IScalar x s = .ok z ∧
      z.val = (x.val <<< s.toNat) % 2^ty.numBits := by
  refine ⟨⟨x.bv.shiftLeft s.toNat⟩, ?_, ?_⟩
  · simp only [UScalar.shiftLeft_IScalar, h0, if_pos,
      UScalar.shiftLeft, hs]
  · exact BitVec.toNat_shiftLeft

theorem negative_counts_fail {ty tys} (x : UScalar ty) (s : IScalar tys)
    (h : s.val < 0) :
    UScalar.shiftLeft_IScalar x s = .fail .integerOverflow ∧
    UScalar.shiftRight_IScalar x s = .fail .integerOverflow := by
  simp only [UScalar.shiftLeft_IScalar, UScalar.shiftRight_IScalar,
    show ¬s.val ≥ 0 from Int.not_le.mpr h, if_false, and_self]

theorem or_value {ty} (x y : UScalar ty) :
    (UScalar.or x y).val = x.val ||| y.val := BitVec.toNat_or _ _

#print axioms right_success
#print axioms left_success
#print axioms negative_counts_fail
#print axioms or_value
end AspisV8R17.SignedShiftSlice
