import SDX_Cohort
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace SDX_Audit

theorem kit_cohort_disagreement :
    SDX_Join_Release.sampler.low_base_p_digits SDX_PResult.block ≠
      AspisR1Post25Sampler.sampler.low_base_p_digits SDX_PResult.block := by
  rw [SDX_PResult.emitted,SDX_Cohort.resultP]
  intro h
  have hv := congrArg (fun p : Array U32 8#usize × U32 => p.2.val) (Result.ok.inj h)
  norm_num at hv

#print axioms kit_cohort_disagreement
#print axioms SDX_PResult.emitted
#print axioms SDX_ZeroResult.emitted
#print axioms SDX_P1Result.emitted
#print axioms SDX_FFResult.emitted
#print axioms SDX_Cohort.resultP
#print axioms SDX_Cohort.resultZero
#print axioms SDX_Cohort.resultP1
#print axioms SDX_Cohort.resultFF
end SDX_Audit
