import AspisR1ActualSemanticRoundCutV1.Funs
import AspisR1PublicPreparation.Funs
import S9SamplerGuardedOpsV1

set_option autoImplicit false
namespace AspisR1ActualSamplerBodyRefinementV1
open Aeneas Aeneas.Std Result

private theorem wrapping_sub_checked_guard (j : Usize) (hj : 0 < j.val) :
    lift (Std.Usize.wrapping_sub j 1#usize) = (j - 1#usize : Result Usize) := by
  have hs := AspisR1S9SamplerGuardedOpsV1.sub_agree j 1#usize (by change 1 ≤ j.val; omega)
  change (j - 1#usize : Result Usize) =
    .ok (UScalar.wrapping_sub j 1#usize) at hs
  calc
    lift (Std.Usize.wrapping_sub j 1#usize) =
        .ok (UScalar.wrapping_sub j 1#usize) := by
      simp only [Std.Usize.wrapping_sub, lift]
    _ = (j - 1#usize : Result Usize) := hs.symm

/-- The guarded long-division callback agrees for every state. The sole guard
needed for subtraction is the source's own `j > 0`; shift is equal for all r. -/
theorem div_pass_body_eq (rank : Array U32 8#usize) (remainder : U64)
    (j : Usize) :
    AspisR1ActualSemanticRoundCutV1.sampler.qm31_div_pass_loop.body rank remainder j =
    AspisR1PublicPreparation.sampler.qm31_div_pass_loop.body rank remainder j := by
  unfold AspisR1ActualSemanticRoundCutV1.sampler.qm31_div_pass_loop.body
    AspisR1PublicPreparation.sampler.qm31_div_pass_loop.body
  by_cases hguard : j > 0#usize
  · have hj : 0 < j.val := by scalar_tac
    rw [if_pos hguard]
    rw [if_pos hguard]
    rw [wrapping_sub_checked_guard j hj, AspisR1S9SamplerGuardedOpsV1.shift32_agree]
    simp only [AspisR1ActualSemanticRoundCutV1.aspis_core.field.P,
      AspisR1PublicPreparation.aspis_core.field.P,
      lift, bind_tc_ok]
  · rw [if_neg hguard]
    rw [if_neg hguard]

#print axioms wrapping_sub_checked_guard
#print axioms div_pass_body_eq
end AspisR1ActualSamplerBodyRefinementV1
