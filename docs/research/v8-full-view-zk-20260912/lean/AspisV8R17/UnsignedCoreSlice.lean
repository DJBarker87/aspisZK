import Aeneas.Std.Primitives
import AeneasMeta.BvEnumToBitVec
import Mathlib.Data.Nat.Notation

/-! Focused unsigned runtime projection. Blocks marked SOURCE are authenticated
against the pinned Aeneas runtime. Do not import with Aeneas.Std.Scalar.Core.
This is not yet an extracted CM31 or R17 caller theorem. -/
namespace Aeneas.Std
open Result Error

-- SOURCE Core.lean
inductive UScalarTy where
| Usize
| U8
| U16
| U32
| U64
| U128
deriving BvEnumToBitVec
-- END SOURCE

-- SOURCE Core.lean
@[implicit_reducible]
def UScalarTy.numBits (ty : UScalarTy) : Nat :=
  match ty with
  | Usize => System.Platform.numBits
  | U8 => 8
  | U16 => 16
  | U32 => 32
  | U64 => 64
  | U128 => 128
-- END SOURCE

-- SOURCE Core.lean
structure UScalar (ty : UScalarTy) where
  /- The internal representation is a bit-vector -/
  bv : BitVec ty.numBits
deriving Repr, BEq, DecidableEq
-- END SOURCE

-- SOURCE Core.lean
def UScalar.val {ty} (x : UScalar ty) : ℕ := x.bv.toNat
-- END SOURCE

-- SOURCE Core.lean
def UScalar.ofNatCore {ty : UScalarTy} (x : Nat) (h : x < 2^ty.numBits) : UScalar ty :=
  { bv := ⟨ x, h ⟩ }
-- END SOURCE

-- SOURCE Core.lean
@[simp] abbrev UScalar.inBounds (ty : UScalarTy) (x : Nat) : Prop :=
  x < 2^ty.numBits
-- END SOURCE

-- SOURCE Core.lean
@[simp] abbrev UScalar.check_bounds (ty : UScalarTy) (x : Nat) : Bool :=
  x < 2^ty.numBits
-- END SOURCE

-- SOURCE Core.lean
theorem UScalar.check_bounds_imp_inBounds {ty : UScalarTy} {x : Nat}
  (h: UScalar.check_bounds ty x) :
  UScalar.inBounds ty x := by
  simp at *; apply h
-- END SOURCE

-- SOURCE Core.lean
def UScalar.tryMkOpt (ty : UScalarTy) (x : Nat) : Option (UScalar ty) :=
  if h:UScalar.check_bounds ty x then
    some (UScalar.ofNatCore x (UScalar.check_bounds_imp_inBounds h))
  else none
-- END SOURCE

-- SOURCE Core.lean
def UScalar.tryMk (ty : UScalarTy) (x : Nat) : Result (UScalar ty) :=
  Result.ofOption (tryMkOpt ty x) integerOverflow
-- END SOURCE

-- SOURCE Ops/Add.lean
def UScalar.add {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  UScalar.tryMk ty (x.val + y.val)
-- END SOURCE

-- SOURCE Ops/Mul.lean
def UScalar.mul {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  UScalar.tryMk ty (x.val * y.val)
-- END SOURCE

end Aeneas.Std

namespace AspisV8R17.UnsignedCoreSlice
open Aeneas.Std

theorem tryMk_success {ty : UScalarTy} (n : Nat) (h : n < 2^ty.numBits) :
    ∃ z : UScalar ty, UScalar.tryMk ty n = .ok z ∧ z.val = n := by
  refine ⟨UScalar.ofNatCore n h, ?_, rfl⟩
  simp [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, h, Result.ofOption]

theorem add_success (x y : UScalar .U64) (h : x.val + y.val < 2^64) :
    ∃ z : UScalar .U64, UScalar.add x y = .ok z ∧ z.val = x.val + y.val :=
  tryMk_success _ h

theorem mul_success (x y : UScalar .U64) (h : x.val * y.val < 2^64) :
    ∃ z : UScalar .U64, UScalar.mul x y = .ok z ∧ z.val = x.val * y.val :=
  tryMk_success _ h

theorem tryMk_overflow {ty : UScalarTy} (n : Nat) (h : ¬n < 2^ty.numBits) :
    UScalar.tryMk ty n = .fail .integerOverflow := by
  simp [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, h, Result.ofOption]

#print axioms tryMk_success
#print axioms add_success
#print axioms mul_success
#print axioms tryMk_overflow
end AspisV8R17.UnsignedCoreSlice
