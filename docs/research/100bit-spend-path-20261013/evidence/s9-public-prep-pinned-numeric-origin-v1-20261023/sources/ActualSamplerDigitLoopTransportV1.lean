import AspisR1ActualSemanticRoundCutV1.Funs
import AspisR1PublicPreparation.Funs
import S9SamplerGuardedOpsV1
import ActualSamplerDivPassTransportV1
import AspisV8R19.SamplerWordRead

set_option autoImplicit false
namespace AspisR1ActualSamplerDigitLoopTransportV1
open Aeneas Aeneas.Std Result ControlFlow

private abbrev small := AspisV8R19.SamplerWordRead.small

private theorem wrapping_four_mul_checked (i : Usize) (hi : i.val < 8) :
    lift (Std.Usize.wrapping_mul 4#usize i) = (4#usize * i : Result Usize) := by
  have hc : (4#usize * i : Result Usize) = .ok (small (4 * i.val) (by omega)) := by
    change UScalar.tryMk .Usize (4 * i.val) = _
    exact AspisV8R19.SamplerWordRead.try_small _ _
  rw [hc]
  simp only [lift, Std.Usize.wrapping_mul]
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [AspisV8R19.SamplerWordRead.small_val,
    UScalar.wrapping_mul_val_eq, UScalar.size]
  have hmod : i.val * 4 % (2 ^ UScalarTy.Usize.numBits) = i.val * 4 := by
    apply Nat.mod_eq_of_lt
    have hb : i.val * 4 ≤ UScalar.cMax .Usize := by
      have := Usize.cMax_bound
      scalar_tac
    exact UScalar.bound_suffices .Usize (i.val * 4) hb
  have h4val : (4#usize).val = 4 := by decide
  rw [h4val]
  change (4 * i.val) % (2 ^ UScalarTy.Usize.numBits) = 4 * i.val
  simpa only [Nat.mul_comm] using hmod

private theorem wrapping_add_checked (w kk : Usize) (_hk : kk.val ≤ 3)
    (hw : w.val + kk.val ≤ 32) :
    lift (Std.Usize.wrapping_add w kk) = (w + kk : Result Usize) := by
  have hc : (w + kk : Result Usize) =
      .ok (small (w.val + kk.val) (by omega)) := by
    change UScalar.tryMk .Usize (w.val + kk.val) = _
    exact AspisV8R19.SamplerWordRead.try_small _ (by omega)
  rw [hc]
  simp only [lift, Std.Usize.wrapping_add]
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [AspisV8R19.SamplerWordRead.small_val,
    UScalar.wrapping_add_val_eq, UScalar.size]
  apply Nat.mod_eq_of_lt
  have hb : w.val + kk.val ≤ UScalar.cMax .Usize := by
    have := Usize.cMax_bound
    scalar_tac
  exact UScalar.bound_suffices .Usize (w.val + kk.val) hb

private theorem add_one_checked (i : Usize) (hi : i.val < 8) :
    lift (Std.Usize.wrapping_add i 1#usize) = (i + 1#usize : Result Usize) := by
  have hc : (i + 1#usize : Result Usize) =
      .ok (small (i.val + 1) (by omega)) := by
    change UScalar.tryMk .Usize (i.val + 1) = _
    exact AspisV8R19.SamplerWordRead.try_small _ (by omega)
  rw [hc]
  simp only [Std.Usize.wrapping_add, lift]
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [AspisV8R19.SamplerWordRead.small_val,
    UScalar.wrapping_add_val_eq, UScalar.size]
  apply Nat.mod_eq_of_lt
  have hb : i.val + 1 ≤ UScalar.cMax .Usize := by
    have := Usize.cMax_bound
    scalar_tac
  exact UScalar.bound_suffices .Usize (i.val + 1) hb

private theorem wrapping_add_value (i : Usize) (hi : i.val < 8) :
    Std.Usize.wrapping_add i 1#usize = small (i.val + 1) (by omega) := by
  have hc : (i + 1#usize : Result Usize) = .ok (small (i.val + 1) (by omega)) := by
    change UScalar.tryMk .Usize (i.val + 1) = _
    exact AspisV8R19.SamplerWordRead.try_small _ (by omega)
  have hn := add_one_checked i hi
  rw [hc] at hn
  change Result.ok (Std.Usize.wrapping_add i 1#usize) =
      Result.ok (small (i.val + 1) (by omega)) at hn
  exact Result.ok.inj hn

private theorem div_pass_eq (rank : Array U32 8#usize) :
    AspisR1ActualSemanticRoundCutV1.sampler.qm31_div_pass rank =
      AspisR1PublicPreparation.sampler.qm31_div_pass rank := by
  unfold AspisR1ActualSemanticRoundCutV1.sampler.qm31_div_pass
    AspisR1PublicPreparation.sampler.qm31_div_pass
  rw [AspisR1ActualSamplerDivPassTransportV1.loop_eq]

theorem digits_loop0_body_eq (block : Array U8 32#usize)
    (rank : Array U32 8#usize) (i : Usize) :
    AspisR1ActualSemanticRoundCutV1.sampler.qm31_digits_loop0.body block rank i =
      AspisR1PublicPreparation.sampler.qm31_digits_loop0.body block rank i := by
  unfold AspisR1ActualSemanticRoundCutV1.sampler.qm31_digits_loop0.body
    AspisR1PublicPreparation.sampler.qm31_digits_loop0.body
  by_cases h : i < 8#usize
  · have hi : i.val < 8 := by scalar_tac
    rw [if_pos h, if_pos h]
    have hm := wrapping_four_mul_checked i hi
    have hcmul : (4#usize * i : Result Usize) =
        .ok (small (4 * i.val) (by omega)) := by
      change UScalar.tryMk .Usize (4 * i.val) = _
      exact AspisV8R19.SamplerWordRead.try_small _ (by omega)
    rw [hm, hcmul]
    simp only [bind_tc_ok]
    -- the three byte offsets are below 32 under the loop guard
    have h1val : (1#usize).val = 1 := by decide
    have h2val : (2#usize).val = 2 := by decide
    have h3val : (3#usize).val = 3 := by decide
    have h1 := wrapping_add_checked (small (4 * i.val) (by omega)) 1#usize (by decide) (by
      rw [AspisV8R19.SamplerWordRead.small_val, h1val]; omega)
    have h2 := wrapping_add_checked (small (4 * i.val) (by omega)) 2#usize (by decide) (by
      rw [AspisV8R19.SamplerWordRead.small_val, h2val]; omega)
    have h3 := wrapping_add_checked (small (4 * i.val) (by omega)) 3#usize (by decide) (by
      rw [AspisV8R19.SamplerWordRead.small_val, h3val]; omega)
    rw [h1, h2, h3]
    have hcfinal : (i + 1#usize : Result Usize) =
        .ok (small (i.val + 1) (by omega)) := by
      change UScalar.tryMk .Usize (i.val + 1) = _
      exact AspisV8R19.SamplerWordRead.try_small _ (by omega)
    simp only [wrapping_add_value i hi, hcfinal, lift, bind_tc_ok]
  · rw [if_neg h, if_neg h]

theorem digits_loop1_body_eq (rank : Array U32 8#usize)
    (digits : Array U32 4#usize) (i : Usize) :
    AspisR1ActualSemanticRoundCutV1.sampler.qm31_digits_loop1.body rank digits i =
      AspisR1PublicPreparation.sampler.qm31_digits_loop1.body rank digits i := by
  unfold AspisR1ActualSemanticRoundCutV1.sampler.qm31_digits_loop1.body
    AspisR1PublicPreparation.sampler.qm31_digits_loop1.body
  by_cases h : i < 4#usize
  · have hi : i.val < 4 := by scalar_tac
    rw [if_pos h, if_pos h, div_pass_eq]
    have hn := add_one_checked i (by omega)
    rw [hn]
  · rw [if_neg h, if_neg h]

#print axioms digits_loop0_body_eq
#print axioms digits_loop1_body_eq
end AspisR1ActualSamplerDigitLoopTransportV1
