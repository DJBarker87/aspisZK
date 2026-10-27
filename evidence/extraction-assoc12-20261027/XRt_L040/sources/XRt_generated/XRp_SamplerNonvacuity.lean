import XRp_LowSamplerObstruction
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_SamplerNonvacuity
open XRp_SamplerSeed XRp_SamplerRepeated XRp_LowSamplerObstruction

theorem both_succeed : ∃ ds : Array U32 8#usize, ∃ q : U32,
    XRn_Join_Release.sampler.low_base_p_digits block = ok (zeros,2147483647#u32) ∧
    AspisR1Post25Sampler.sampler.low_base_p_digits block = ok (ds,q) ∧
    q.val ≤ 256 ∧
    XRn_Join_Release.sampler.low_base_p_digits block ≠
      AspisR1Post25Sampler.sampler.low_base_p_digits block := by
  obtain ⟨_,ds,q,run,_,_,_⟩ :=
    AspisR1.ExtractedQM31SamplerIndexedOutputSuccessV5.low_base_p_digits_success block
  exact ⟨ds,q,emitted_low,run,candidate_bound block ds q run,sampler_commutation_false⟩

#print axioms both_succeed
end XRp_SamplerNonvacuity
