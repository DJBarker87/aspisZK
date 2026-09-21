import AspisV8R17.UnsignedCM31Cross
import Aeneas.Tactic.Step.Init

/-! Authenticated scalar operations needed by the current reduce_u64 graph.
This leaf does not yet compose the complete reducer. -/
namespace Aeneas.Std
open Result Error

-- SOURCE Casts.lean
@[step_pure_def]
def UScalar.cast {src_ty : UScalarTy} (tgt_ty : UScalarTy) (x : UScalar src_ty) : UScalar tgt_ty :=
  -- This truncates the integer if the numBits is smaller
  ⟨ x.bv.zeroExtend tgt_ty.numBits ⟩
-- END SOURCE

-- SOURCE Bitwise.lean
def UScalar.shiftRight {ty : UScalarTy} (x : UScalar ty) (s : Nat) :
  Result (UScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.bv.ushiftRight s ⟩
  else fail .integerOverflow
-- END SOURCE

-- SOURCE Bitwise.lean
def UScalar.shiftRight_UScalar {ty tys} (x : UScalar ty) (s : UScalar tys) :
  Result (UScalar ty) :=
  x.shiftRight s.val
-- END SOURCE

-- SOURCE Bitwise.lean
def UScalar.and {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv &&& y.bv ⟩
-- END SOURCE

-- SOURCE Ops/Sub.lean
def UScalar.sub {ty : UScalarTy} (x y : UScalar ty) : Result (UScalar ty) :=
  if x.val < y.val then fail .integerOverflow
  else ok ⟨ BitVec.ofNat _ (x.val - y.val) ⟩
-- END SOURCE
end Aeneas.Std

namespace AspisV8R17.UnsignedReducerOps
open Aeneas.Std

theorem cast_value {ty : UScalarTy} (x : UScalar ty) (target : UScalarTy) :
    (UScalar.cast target x).val = x.val % 2^target.numBits := by
  exact BitVec.toNat_setWidth _ _

theorem narrow_exact (x : U64) (h : x.val < 2^32) :
    (UScalar.cast .U32 x).val = x.val := by
  rw [cast_value]
  exact Nat.mod_eq_of_lt h

theorem and_value {ty : UScalarTy} (x y : UScalar ty) :
    (UScalar.and x y).val = x.val &&& y.val :=
  BitVec.toNat_and _ _

theorem shift_success {ty : UScalarTy} (x : UScalar ty) (s : Nat) (h : s < ty.numBits) :
    ∃ z : UScalar ty, UScalar.shiftRight x s = .ok z ∧ z.val = x.val >>> s := by
  refine ⟨⟨x.bv.ushiftRight s⟩, ?_, BitVec.toNat_ushiftRight _ _⟩
  simp only [UScalar.shiftRight, h, if_pos]

theorem sub_success {ty : UScalarTy} (x y : UScalar ty) (h : y.val ≤ x.val) :
    ∃ z : UScalar ty, UScalar.sub x y = .ok z ∧ z.val = x.val-y.val := by
  refine ⟨⟨BitVec.ofNat _ (x.val-y.val)⟩, ?_, ?_⟩
  · simp only [UScalar.sub, Nat.not_lt.mpr h, if_false]
  · change (x.val-y.val) % 2^ty.numBits = x.val-y.val
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.bv.isLt

theorem shift_overflow {ty : UScalarTy} (x : UScalar ty) (s : Nat) (h : ¬s < ty.numBits) :
    UScalar.shiftRight x s = .fail .integerOverflow := by
  simp only [UScalar.shiftRight, h, if_false]

theorem sub_underflow {ty : UScalarTy} (x y : UScalar ty) (h : x.val < y.val) :
    UScalar.sub x y = .fail .integerOverflow := by
  simp only [UScalar.sub, h, if_pos]

#print axioms cast_value
#print axioms narrow_exact
#print axioms and_value
#print axioms shift_success
#print axioms sub_success
#print axioms shift_overflow
#print axioms sub_underflow
end AspisV8R17.UnsignedReducerOps
