import S3ActualLoop0SuccessPrefixCompositionV1
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1GroupedPairActualFieldOpsV3.ActualLoop1

open AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete
open AspisR1GroupedPairActualFieldOpsV3.SuccessPrefixComposition

abbrev M := AspisWideTower.WideExact

/-- A source-shaped low-mask fold.  `bit` is the position of the head in the
remaining slice; each item contributes exactly when the corresponding bit of
the selected mask is set. -/
def maskedFold (mask : Nat) : Nat → List M → M
  | _, [] => 0
  | bit, x :: xs =>
      (if (mask / 2 ^ bit) % 2 = 1 then x else 0) + maskedFold mask (bit + 1) xs

theorem maskedFold_cons (mask bit : Nat) (x : M) (xs : List M) :
    maskedFold mask bit (x :: xs) =
      (if (mask / 2 ^ bit) % 2 = 1 then x else 0) +
        maskedFold mask (bit + 1) xs := rfl

/-- The actual U16 shift and and results select exactly the corresponding
integer mask bit.  The shift-index bound comes from the 16-element slice. -/
theorem actual_mask_test_matches_bit
    (mask power bitResult : Std.U16) (bit : Std.Usize)
    (hbit : bit.val < 16)
    (hshift : (1#u16 <<< bit : Result Std.U16) = .ok power)
    (hand : lift (mask &&& power) = .ok bitResult) :
    (bitResult != 0#u16) ↔ (mask.val / 2 ^ bit.val) % 2 = 1 := by
  have hshiftSpec := UScalar.ShiftLeft_spec (1#u16) bit
    (UScalar.size UScalarTy.U16)
    (by
      change bit.val < UScalarTy.U16.numBits
      have hwidth : UScalarTy.U16.numBits = 16 := by decide
      rw [hwidth]
      exact hbit)
    rfl
  obtain ⟨shifted, hshiftRun, hshiftValue⟩ := WP.spec_imp_exists hshiftSpec
  have hshiftedPower : shifted = power := Result.ok.inj (hshiftRun.symm.trans hshift)
  have hone : (1#u16).val = 1 := by norm_num [UScalar.ofNatCore_val_eq]
  have hsize : UScalar.size UScalarTy.U16 = 2 ^ 16 := by
    rw [UScalar.size_UScalarTyU16, U16.size]
    rw [U16.numBits, UScalarTy.U16_numBits_eq]
  have hpowBound16 : 2 ^ bit.val < 2 ^ 16 := by
    exact Nat.pow_lt_pow_right (by decide) hbit
  have hpowBound : 2 ^ bit.val < UScalar.size UScalarTy.U16 := by
    rw [hsize]
    exact hpowBound16
  have hpow : power.val = 2 ^ bit.val := by
    have hpval : power.val = shifted.val :=
      congrArg UScalar.val hshiftedPower.symm
    calc
      power.val = shifted.val := hpval
      _ = (1#u16).val <<< bit.val % UScalar.size UScalarTy.U16 := hshiftValue.1
      _ = (1 * 2 ^ bit.val) % 2 ^ 16 := by
        rw [hone, Nat.shiftLeft_eq, hsize]
      _ = 2 ^ bit.val := by
        rw [Nat.one_mul]
        exact Nat.mod_eq_of_lt hpowBound16
  have handEq : mask &&& power = bitResult := by
    change Result.ok (mask &&& power) = Result.ok bitResult at hand
    exact Result.ok.inj hand
  have handVal : bitResult.val = mask.val &&& power.val := by
    rw [← handEq]
    exact UScalar.val_and _ _
  have hneBool : (bitResult != 0#u16) = true ↔ bitResult ≠ 0#u16 := by simp
  have hneVal : bitResult ≠ 0#u16 ↔ bitResult.val ≠ 0 := by
    constructor
    · intro h
      intro hv
      apply h
      apply UScalar.eq_of_val_eq
      have hz : bitResult.val = (0#u16).val := by
        simpa [UScalar.ofNatCore_val_eq] using hv
      exact hz
    · intro h
      intro hz
      apply h
      have hv := congrArg UScalar.val hz
      simpa [UScalar.ofNatCore_val_eq] using hv
  have hbitEq : (bitResult != 0#u16) = true ↔ bitResult.val ≠ 0 :=
    hneBool.trans hneVal
  have handPow : mask.val &&& 2 ^ bit.val =
      (mask.val.testBit bit.val).toNat * 2 ^ bit.val := by
    have h := Nat.and_two_pow mask.val bit.val
    simpa using h
  have htestModel : (mask.val.testBit bit.val).toNat =
      (mask.val / 2 ^ bit.val) % 2 := by
    have hsmall : (mask.val / 2 ^ bit.val) % 2 < 2 :=
      Nat.mod_lt _ (by decide)
    rw [Nat.testBit_eq_decide_div_mod_eq]
    simp only [Bool.toNat]
    by_cases h : (mask.val / 2 ^ bit.val) % 2 = 1
    · simp [h]
    · simp [h]
      omega
  have hpowPos : 0 < 2 ^ bit.val := Nat.pow_pos (by decide)
  have hprod :
      ((mask.val.testBit bit.val).toNat * 2 ^ bit.val ≠ 0) ↔
        (mask.val.testBit bit.val).toNat ≠ 0 := by
    constructor
    · intro hp hzero
      rw [hzero] at hp
      simp at hp
    · intro hbitNonzero hp
      apply hbitNonzero
      rcases Nat.mul_eq_zero.mp hp with ha | hb
      · exact ha
      · exact False.elim ((Nat.ne_of_gt hpowPos) hb)
  have hmodNonzero :
      (mask.val / 2 ^ bit.val) % 2 ≠ 0 ↔
        (mask.val / 2 ^ bit.val) % 2 = 1 := by
    have hlt := Nat.mod_lt (mask.val / 2 ^ bit.val) (by decide : 0 < 2)
    omega
  rw [hbitEq, handVal, hpow, handPow]
  have htestBool : (mask.val.testBit bit.val).toNat ≠ 0 ↔
      (mask.val / 2 ^ bit.val) % 2 = 1 := by
    rw [htestModel]
    exact hmodNonzero
  exact hprod.trans htestBool

/-- One successful iteration of the actual emitted 16-entry loop.  The
premises name each checked Rust/Aeneas operation, while the conclusion ties
the returned weight to the exact bit-selected semantic contribution. -/
theorem body_some_step
    (group : Std.Usize)
    (ops : Operations)
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter field.WideExact))
    (weight challenge nextWeight : field.WideExact)
    (iterNext : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter field.WideExact))
    (mask power bitResult : Std.U16)
    (bit : Std.Usize)
    (hnext : core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter field.WideExact) iter =
      .ok (some (bit, challenge), iterNext))
    (hmask : Array.index_usize weights.S2_INACTIVE_MASKS group = .ok mask)
    (hshift : (1#u16 <<< bit : Result Std.U16) = .ok power)
    (hand : lift (mask &&& power) = .ok bitResult)
    (hselectedModel : (bitResult != 0#u16) ↔
      (mask.val / 2 ^ bit.val) % 2 = 1)
    (hadd : ops.add weight challenge = .ok nextWeight)
    (hdecode : decode nextWeight = decode weight + decode challenge) :
    weights.s2_grouped_inactive_pair_loop1_loop0.body ops group iter weight =
      .ok (.cont (iterNext, if bitResult != 0#u16 then nextWeight else weight)) ∧
    decode (if bitResult != 0#u16 then nextWeight else weight) =
      decode weight +
        (if ((mask.val / 2 ^ bit.val) % 2 = 1) then decode challenge else 0) := by
  constructor
  · rw [weights.s2_grouped_inactive_pair_loop1_loop0.body, hnext, hmask]
    change (do
      let i1 ← (1#u16 <<< bit : Result Std.U16)
      let i2 ← lift (mask &&& i1)
      if i2 != 0#u16 then do
        let weight1 ← ops.add weight challenge
        ok (cont (iterNext, weight1))
      else ok (cont (iterNext, weight))) =
        .ok (.cont (iterNext, if bitResult != 0#u16 then nextWeight else weight))
    by_cases htest : bitResult != 0#u16
    · rw [hshift]
      simp only [bind_tc_ok]
      rw [hand]
      simp only [bind_tc_ok, if_pos htest, hadd]
    · rw [hshift]
      simp only [bind_tc_ok]
      rw [hand]
      simp only [bind_tc_ok, if_neg htest]
  · by_cases htest : bitResult != 0#u16
    · have hmodel := hselectedModel.mp htest
      simp [htest, hdecode, hmodel]
    · have hmodel : (mask.val / 2 ^ bit.val) % 2 ≠ 1 := by
        intro h
        exact htest (hselectedModel.mpr h)
      simp [htest, hmodel]

end AspisR1GroupedPairActualFieldOpsV3.ActualLoop1

#print axioms AspisR1GroupedPairActualFieldOpsV3.ActualLoop1.maskedFold_cons
#print axioms AspisR1GroupedPairActualFieldOpsV3.ActualLoop1.body_some_step
