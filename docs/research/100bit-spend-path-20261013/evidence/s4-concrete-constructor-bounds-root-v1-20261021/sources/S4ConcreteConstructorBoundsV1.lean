import AspisR1AccumulatorNewConcreteChildrenV4
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisR1S4ConcreteConstructorBoundsV1
open AspisR1S4AccumulatorNewConcreteChildrenV4
-- Reuses the symbolic multiplication/shift proofs in Tx1FinalLenBoundV8.
private theorem small_max (n : Nat) (hn : n < 2048) : n ≤ Usize.max := by
  have hpow : n < 2 ^ UScalarTy.Usize.numBits := by
    rw [UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
    have hmax := Usize.cMax_bound_concrete.1
    omega
  have hsucc : n < Usize.max + 1 := by
    simpa only [UScalarTy.Usize_numBits_eq, Usize.max_succ_eq_pow] using hpow
  omega
private theorem mul21 : (2#usize * 1#usize : Result Usize) = .ok (2#usize) := by
  have hs : (2#usize * 1#usize : Result Usize) ⦃z => z.val = 2⦄ := by
    apply UScalar.mul_spec
    simpa only [UScalar.max_USize_eq, UScalar.ofNatCore_val_eq] using small_max 2 (by omega)
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists hs
  have heq : z = 2#usize := UScalar.eq_of_val_eq (by simpa using hv)
  simpa [heq] using hz
private theorem mul22 : (2#usize * 2#usize : Result Usize) = .ok (4#usize) := by
  have hs : (2#usize * 2#usize : Result Usize) ⦃z => z.val = 4⦄ := by
    apply UScalar.mul_spec
    simpa only [UScalar.max_USize_eq, UScalar.ofNatCore_val_eq] using small_max 4 (by omega)
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists hs
  have heq : z = 4#usize := UScalar.eq_of_val_eq (by simpa using hv)
  simpa [heq] using hz
private theorem shift2 : (1024#usize >>> 2#usize : Result Usize) = .ok (256#usize) := by
  have hlevel : (2#usize).val < UScalarTy.Usize.numBits := by
    rw [UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h32 | h64
    · rw [h32]; norm_num [UScalar.ofNatCore_val_eq]
    · rw [h64]; norm_num [UScalar.ofNatCore_val_eq]
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists
    (UScalar.ShiftRight_spec (1024#usize) (2#usize) hlevel)
  have hv' : z.val = (256#usize).val := by
    rw [hv.1]
    norm_num [UScalar.ofNatCore_val_eq, Nat.shiftRight_eq_div_pow]
  have heq : z = 256#usize := UScalar.eq_of_val_eq hv'
  simpa [heq] using hz
private theorem shift4 : (1024#usize >>> 4#usize : Result Usize) = .ok (64#usize) := by
  have hlevel : (4#usize).val < UScalarTy.Usize.numBits := by
    rw [UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h32 | h64
    · rw [h32]; norm_num [UScalar.ofNatCore_val_eq]
    · rw [h64]; norm_num [UScalar.ofNatCore_val_eq]
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists
    (UScalar.ShiftRight_spec (1024#usize) (4#usize) hlevel)
  have hv' : z.val = (64#usize).val := by
    rw [hv.1]
    norm_num [UScalar.ofNatCore_val_eq, Nat.shiftRight_eq_div_pow]
  have heq : z = 64#usize := UScalar.eq_of_val_eq hv'
  simpa [heq] using hz


theorem source_final_len_cases (v : Variant) :
    sourceFinalLen v = match v with
      | .S1 => .ok 256#usize
      | .S2 => .ok 64#usize
      | .D => .ok 64#usize := by
  cases v <;> simp [sourceFinalLen, sourceFolds, sourceVariantEq,
    variantToSource, mul21, mul22, shift2, shift4]

theorem source_final_len_total_and_bounded (v : Variant) :
    ∃ n : Usize, sourceFinalLen v = .ok n ∧ n.val ≤ 256 := by
  cases v <;> simp only [source_final_len_cases]
  all_goals exact ⟨_,rfl,by norm_num [UScalar.ofNatCore_val_eq]⟩

#print axioms source_final_len_cases
#print axioms source_final_len_total_and_bounded
end AspisR1S4ConcreteConstructorBoundsV1
