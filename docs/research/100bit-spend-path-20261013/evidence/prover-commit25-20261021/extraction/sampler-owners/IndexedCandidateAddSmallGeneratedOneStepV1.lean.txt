import AspisR1Post25SamplerIndexedAddSmallCandidate.Funs

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error WP
open AspisR1Post25SamplerIndexedAddSmallCandidate

namespace AspisR1.ExtractedIndexedAddSmallGeneratedOneStepV2

abbrev Digits := Array Std.U32 8#usize
private abbrev P : Nat := 2147483647

private theorem source_P_val : field.P.val = P := by
  rw [field.P]
  rfl

private theorem P_pos : 0 < P := by norm_num [P]

/-- The emitted indexed candidate loop body succeeds in source order. This
keeps the array write between the remainder and quotient operations, exactly
as in the checked Aeneas owner. -/
theorem body_step (digits : Digits) (addend : U32) (i : Usize)
    (digit : U32) (hi : i.val < 8)
    (hindex : Array.index_usize digits i = .ok digit)
    (hdigit : digit.val < P)
    (haddend : addend.val ≤ 257) :
    ∃ digitOut carryOut next,
      sampler.add_small_base_p_loop.body digits addend i =
        .ok (.cont (digits.set i digitOut, carryOut, next)) ∧
      digitOut.val = (digit.val + addend.val) % P ∧
      carryOut.val = (digit.val + addend.val) / P ∧
      next.val = i.val + 1 := by
  let d64 : U64 := core.convert.num.FromU64U32.from digit
  let a64 : U64 := core.convert.num.FromU64U32.from addend
  let p64 : U64 := core.convert.num.FromU64U32.from field.P
  have hd64 : d64.val = digit.val := by
    simp only [d64, core.convert.num.FromU64U32.from_val_eq]
  have ha64 : a64.val = addend.val := by
    simp only [a64, core.convert.num.FromU64U32.from_val_eq]
  have hfromDigit : lift (core.convert.num.FromU64U32.from digit) = .ok d64 := by rfl
  have hfromAddend : lift (core.convert.num.FromU64U32.from addend) = .ok a64 := by rfl
  have hfromP : lift (core.convert.num.FromU64U32.from field.P) = .ok p64 := by rfl
  have hp64 : p64.val = P := by
    simp only [p64, core.convert.num.FromU64U32.from_val_eq, source_P_val]
  have hsmall : digit.val + addend.val < 2^32 := by
    have hcap : P + 257 < 2^32 := by norm_num [P]
    omega
  have hsumBound : d64.val + a64.val ≤ U64.max := by
    rw [hd64, ha64]
    have hcap : (2 : Nat)^32 ≤ U64.max := by norm_num [U64.max, U64.numBits]
    exact le_trans (Nat.le_of_lt hsmall) hcap
  have hsumSpec : (d64 + a64 : Result U64) ⦃z => z.val = d64.val + a64.val⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_UScalarTy_U64_eq] using hsumBound
  obtain ⟨sum, hsum, hsumVal⟩ := WP.spec_imp_exists hsumSpec
  have hsumVal' : sum.val = digit.val + addend.val := by
    rw [hsumVal, hd64, ha64]
  have hpNonzero : p64.val ≠ 0 := by
    rw [hp64]
    exact Nat.ne_of_gt P_pos
  obtain ⟨rem, hrem, hremVal⟩ :=
    WP.spec_imp_exists (UScalar.rem_spec sum hpNonzero)
  obtain ⟨quo, hquo, hquoVal⟩ := UScalar.div_spec sum hpNonzero
  have hremVal' : rem.val = (digit.val + addend.val) % P := by
    rw [hremVal, hsumVal', hp64]
  have hquoVal' : quo.val = (digit.val + addend.val) / P := by
    rw [hquoVal, hsumVal', hp64]
  have hremBound : rem.val ≤ UScalar.max UScalarTy.U32 := by
    rw [hremVal']
    have hlt : (digit.val + addend.val) % P < P := Nat.mod_lt _ P_pos
    have hP32 : P ≤ UScalar.max UScalarTy.U32 := by
      rw [UScalar.max_UScalarTy_U32_eq]
      norm_num [P, U32.max, U32.numBits]
    omega
  have hquoBound : quo.val ≤ UScalar.max UScalarTy.U32 := by
    rw [hquoVal']
    have hsumSmall : digit.val + addend.val < 2 * P := by
      have hcap : P + 257 < 2 * P := by norm_num [P]
      omega
    have hq : (digit.val + addend.val) / P ≤ 1 := by
      have hp : 0 < P := P_pos
      have hq' : (digit.val + addend.val) / P < 2 :=
        (Nat.div_lt_iff_lt_mul hp).2 (by simpa [Nat.mul_comm] using hsumSmall)
      omega
    have hU32 : 1 ≤ UScalar.max UScalarTy.U32 := by
      rw [UScalar.max_UScalarTy_U32_eq]
      norm_num [U32.max, U32.numBits]
    omega
  obtain ⟨digitOut, hcastRem, hcastRemVal⟩ :=
    WP.spec_imp_exists (UScalar.cast_inBounds_spec .U32 rem hremBound)
  obtain ⟨carryOut, hcastQuo, hcastQuoVal⟩ :=
    WP.spec_imp_exists (UScalar.cast_inBounds_spec .U32 quo hquoBound)
  have hmax : UScalar.max UScalarTy.U32 = 2^32 - 1 := by
    norm_num [UScalar.max_UScalarTy_U32_eq, U32.max, U32.numBits]
  have hremExact : (UScalar.cast .U32 rem).val = rem.val := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    have hmaxLt : UScalar.max UScalarTy.U32 < 2^32 := by
      rw [hmax]
      norm_num
    exact lt_of_le_of_lt hremBound hmaxLt
  have hquoExact : (UScalar.cast .U32 quo).val = quo.val := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    have hmaxLt : UScalar.max UScalarTy.U32 < 2^32 := by
      rw [hmax]
      norm_num
    exact lt_of_le_of_lt hquoBound hmaxLt
  have hdigitEq : UScalar.cast .U32 rem = digitOut :=
    UScalar.eq_of_val_eq (by rw [hremExact]; exact hcastRemVal.symm)
  have hcarryEq : UScalar.cast .U32 quo = carryOut :=
    UScalar.eq_of_val_eq (by rw [hquoExact]; exact hcastQuoVal.symm)
  have hdigitOut : digitOut.val = (digit.val + addend.val) % P := by
    rw [hcastRemVal, hremVal']
  have hcarryOut : carryOut.val = (digit.val + addend.val) / P := by
    rw [hcastQuoVal, hquoVal']
  have harrayBound : i.val < digits.length := by
    have hlen : digits.length = 8 := digits.property
    omega
  obtain ⟨updated, hup, hset⟩ :=
    WP.spec_imp_exists (Array.update_spec digits i digitOut harrayBound)
  have hupdate : Array.update digits i digitOut = .ok (digits.set i digitOut) :=
    hup.trans (congrArg Result.ok hset)
  obtain ⟨next, hn, hnext⟩ :=
    WP.spec_imp_exists (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
  have hlt : i < 8#usize := hi
  refine ⟨digitOut, carryOut, next, ?_, hdigitOut, hcarryOut, ?_⟩
  · unfold sampler.add_small_base_p_loop.body
    simp only [if_pos hlt, hindex, bind_tc_ok, hfromDigit, hfromAddend,
      hsum, hfromP, hrem, hcastRem, hupdate, hfromP, hquo, hcastQuo, hn]
  · simpa using hnext

#print axioms body_step

end AspisR1.ExtractedIndexedAddSmallGeneratedOneStepV2
