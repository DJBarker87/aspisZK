import S9S3U16ShiftCompatV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9S3MaskBitReadOnlyV1

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


/-- The current native shim selects exactly the EXISTING S3 integer mask bit.
The checked-shift witness is derived from the actual bit<16 loop domain. -/
theorem native_mask_test_matches_bit (mask : U16) (bit : Usize) (hbit : bit.val<16) :
    ((mask &&& AspisR1S9ShiftCountCompatV1.u16Shl 1#u16 bit) != 0#u16) ↔
      (mask.val / 2^bit.val)%2=1 := by
  exact actual_mask_test_matches_bit mask
    (AspisR1S9ShiftCountCompatV1.u16Shl 1#u16 bit)
    (mask &&& AspisR1S9ShiftCountCompatV1.u16Shl 1#u16 bit) bit hbit
    (AspisR1S9S3U16ShiftCompatV1.checked_u16_shl_compat 1#u16 bit hbit) rfl

#print axioms actual_mask_test_matches_bit
#print axioms native_mask_test_matches_bit
end AspisR1S9S3MaskBitReadOnlyV1
