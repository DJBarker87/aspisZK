import Aeneas
import TerminalV4ActiveLiteralClosureV2

/-!
Source-only port of unsigned scalar facts to the actual Aeneas runtime imported
by the current QM31 arithmetic probe.  This file deliberately defines no
runtime types or operations.
-/
set_option autoImplicit false
namespace AspisR1.TerminalV4ReducerOps

open Aeneas.Std
open Result Error

theorem cast_value {ty : UScalarTy} (x : UScalar ty) (target : UScalarTy) :
    (UScalar.cast target x).val = x.val % 2^target.numBits := by
  exact UScalar.cast_val_eq target x

theorem narrow_exact (x : U64) (h : x.val < 2^32) :
    (UScalar.cast .U32 x).val = x.val := by
  rw [cast_value]
  exact Nat.mod_eq_of_lt h

theorem and_value {ty : UScalarTy} (x y : UScalar ty) :
    (UScalar.and x y).val = x.val &&& y.val := by
  exact UScalar.val_and x y

theorem shift_success {ty : UScalarTy} (x : UScalar ty) (s : Nat)
    (h : s < ty.numBits) :
    ∃ z : UScalar ty, UScalar.shiftRight x s = .ok z ∧ z.val = x.val >>> s := by
  refine ⟨⟨x.bv.ushiftRight s⟩, ?_, BitVec.toNat_ushiftRight _ _⟩
  simp only [UScalar.shiftRight, h, if_pos]

theorem sub_success {ty : UScalarTy} (x y : UScalar ty)
    (h : y.val ≤ x.val) :
    ∃ z : UScalar ty, UScalar.sub x y = .ok z ∧ z.val = x.val - y.val := by
  refine ⟨⟨BitVec.ofNat _ (x.val - y.val)⟩, ?_, ?_⟩
  · simp only [UScalar.sub, Nat.not_lt.mpr h, if_false]
  · change (x.val - y.val) % 2^ty.numBits = x.val - y.val
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.bv.isLt

theorem tryMk_success {ty : UScalarTy} (n : Nat)
    (h : n < 2^ty.numBits) :
    ∃ z : UScalar ty, UScalar.tryMk ty n = .ok z ∧ z.val = n := by
  refine ⟨UScalar.ofNatCore n h, ?_, rfl⟩
  simp [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, h, Result.ofOption]

theorem add_success (x y : U64) (h : x.val + y.val < 2^64) :
    ∃ z : U64, UScalar.add x y = .ok z ∧ z.val = x.val + y.val := by
  exact tryMk_success _ h

theorem mul_success (x y : U64) (h : x.val * y.val < 2^64) :
    ∃ z : U64, UScalar.mul x y = .ok z ∧ z.val = x.val * y.val := by
  exact tryMk_success _ h

#print axioms cast_value
#print axioms narrow_exact
#print axioms and_value
#print axioms shift_success
#print axioms sub_success
#print axioms tryMk_success
#print axioms add_success
#print axioms mul_success

end AspisR1.TerminalV4ReducerOps
