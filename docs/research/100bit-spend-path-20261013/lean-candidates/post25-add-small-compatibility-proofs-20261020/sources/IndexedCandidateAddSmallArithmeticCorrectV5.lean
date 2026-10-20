import IndexedCandidateAddSmallLoopWritebackV1

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error WP
open AspisR1Post25Sampler
open AspisR1.ExtractedAddSmallLoopWritebackV1

namespace AspisR1.ExtractedAddSmallArithmeticCorrectV1

private abbrev P : Nat := 2147483647

private theorem source_P_val : field.P.val = P := by
  rw [field.P]
  rfl

private theorem P_pos : 0 < P := by norm_num [P]

/-- The generated `some digit` arithmetic branch succeeds for canonical
base-P digits and the actual 257 carry bound, and returns the exact Euclidean
remainder and quotient. -/
theorem arithmeticStep_success (digit addend : Std.U32)
    (hdigit : digit.val < P) (haddend : addend.val ≤ 257) :
    ∃ digitOut carryOut,
      arithmeticStep digit addend = .ok (digitOut, carryOut) ∧
      digitOut.val = (digit.val + addend.val) % P ∧
      carryOut.val = (digit.val + addend.val) / P := by
  let i : U64 := core.convert.num.FromU64U32.from digit
  let i1 : U64 := core.convert.num.FromU64U32.from addend
  have hi : i.val = digit.val := by
    simp only [i, core.convert.num.FromU64U32.from_val_eq]
  have hi1 : i1.val = addend.val := by
    simp only [i1, core.convert.num.FromU64U32.from_val_eq]
  have hsmall : digit.val + addend.val < 2^32 := by
    have hcap : P + 257 < 2^32 := by norm_num [P]
    omega
  have hsumBound : i.val + i1.val ≤ U64.max := by
    rw [hi, hi1]
    have hcap : (2 : Nat)^32 ≤ U64.max := by norm_num [U64.max, U64.numBits]
    exact Nat.le_of_lt (lt_of_lt_of_le hsmall hcap)
  have hsumSpec : (i + i1 : Result U64) ⦃z => z.val = i.val + i1.val⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_UScalarTy_U64_eq] using hsumBound
  obtain ⟨sum, hsum, hsumVal⟩ := WP.spec_imp_exists hsumSpec
  have hsumVal' : sum.val = digit.val + addend.val := by
    rw [hsumVal, hi, hi1]
  let p64 : U64 := core.convert.num.FromU64U32.from field.P
  have hp64 : p64.val = P := by
    simp only [p64, core.convert.num.FromU64U32.from_val_eq, source_P_val]
  have hpNonzero : p64.val ≠ 0 := by rw [hp64]; exact Nat.ne_of_gt P_pos
  obtain ⟨rem, hrem, hremVal⟩ :=
    WP.spec_imp_exists (UScalar.rem_spec sum hpNonzero)
  obtain ⟨quo, hquo, hquoVal⟩ := UScalar.div_spec sum hpNonzero
  have hremVal' : rem.val = (digit.val + addend.val) % P := by
    rw [hremVal, hsumVal', hp64]
  have hquoVal' : quo.val = (digit.val + addend.val) / P := by
    rw [hquoVal, hsumVal', hp64]
  have hremBound : rem.val ≤ UScalar.max UScalarTy.U32 := by
    rw [hremVal']
    have hlt : (digit.val + addend.val) % P < P := Nat.mod_lt _ (by norm_num [P])
    have hP32 : P ≤ UScalar.max UScalarTy.U32 := by
      rw [UScalar.max_UScalarTy_U32_eq]
      norm_num [P, U32.max, U32.numBits]
    omega
  have hquoBound : quo.val ≤ UScalar.max UScalarTy.U32 := by
    rw [hquoVal']
    have hq : (digit.val + addend.val) / P ≤ 1 := by
      have hsmall' : digit.val + addend.val < 2 * P := by
        have hcap : P + 257 < 2 * P := by norm_num [P]
        omega
      have hp : 0 < P := by norm_num [P]
      have hq' : (digit.val + addend.val) / P < 2 := by
        exact (Nat.div_lt_iff_lt_mul hp).2 (by simpa [Nat.mul_comm] using hsmall')
      omega
    have hU32 : 1 ≤ UScalar.max UScalarTy.U32 := by
      rw [UScalar.max_UScalarTy_U32_eq]
      norm_num [U32.max, U32.numBits]
    omega
  obtain ⟨digitOut, hcastRem, hcastRemVal⟩ :=
    WP.spec_imp_exists (UScalar.cast_inBounds_spec .U32 rem hremBound)
  obtain ⟨carryOut, hcastQuo, hcastQuoVal⟩ :=
    WP.spec_imp_exists (UScalar.cast_inBounds_spec .U32 quo hquoBound)
  have hcastRemExact : (UScalar.cast .U32 rem).val = rem.val := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    have hmax : UScalar.max UScalarTy.U32 = 2^32 - 1 := by
      norm_num [UScalar.max_UScalarTy_U32_eq, U32.max, U32.numBits]
    have hb : rem.val < 2^32 := by rw [hmax] at hremBound; omega
    exact hb
  have hcastQuoExact : (UScalar.cast .U32 quo).val = quo.val := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    have hmax : UScalar.max UScalarTy.U32 = 2^32 - 1 := by
      norm_num [UScalar.max_UScalarTy_U32_eq, U32.max, U32.numBits]
    have hb : quo.val < 2^32 := by rw [hmax] at hquoBound; omega
    exact hb
  have hcastRemEq : UScalar.cast .U32 rem = digitOut :=
    UScalar.eq_of_val_eq (by rw [hcastRemExact]; exact hcastRemVal.symm)
  have hcastQuoEq : UScalar.cast .U32 quo = carryOut :=
    UScalar.eq_of_val_eq (by rw [hcastQuoExact]; exact hcastQuoVal.symm)
  have hdigitOut : digitOut.val = (digit.val + addend.val) % P := by
    rw [hcastRemVal, hremVal']
  have hcarryOut : carryOut.val = (digit.val + addend.val) / P := by
    rw [hcastQuoVal, hquoVal']
  refine ⟨digitOut, carryOut, ?_, hdigitOut, hcarryOut⟩
  unfold arithmeticStep
  simp only [lift, bind_tc_ok, i, i1, hsum, p64, hrem, hquo,
    hcastRemEq, hcastQuoEq]

#print axioms arithmeticStep_success

end AspisR1.ExtractedAddSmallArithmeticCorrectV1
