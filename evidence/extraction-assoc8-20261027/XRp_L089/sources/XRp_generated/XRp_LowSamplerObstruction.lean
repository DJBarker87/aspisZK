import XRp_SeedArray
import XRp_SamplerRepeated
import GammaCandidateLowQuotient
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_LowSamplerObstruction
open XRp_SamplerSeed XRp_DivisionWitness XRp_SamplerRepeated

theorem emitted_low : XRn_Join_Release.sampler.low_base_p_digits block =
    ok (zeros,2147483647#u32) := by
  unfold XRn_Join_Release.sampler.low_base_p_digits
  rw [XRp_SeedArray.init]
  change (do
    let (ds,c) ← XRn_Join_fromFnState 8#usize fn rank
    let q ← Array.index_usize c 0#usize
    ok (ds,q)) = _
  rw [eight_digits]
  rfl

theorem candidate_bound (bytes : Array U8 32#usize) (ds : Array U32 8#usize) (q : U32)
    (run : AspisR1Post25Sampler.sampler.low_base_p_digits bytes = ok (ds,q)) : q.val ≤ 256 := by
  have h := AspisR1GammaCaller.DigitsModel.low_candidate_refines bytes ds q run
  have hb := AspisR1.SamplerMachineBounds.rank_div_P8_le_256
    (AspisR1.SourceSamplerByteRank.rank_lt bytes)
  rw [← h.2] at hb
  exact hb

theorem sampler_commutation_false :
    XRn_Join_Release.sampler.low_base_p_digits block ≠
      AspisR1Post25Sampler.sampler.low_base_p_digits block := by
  intro h
  have hc := h.symm.trans emitted_low
  have hb := candidate_bound block zeros 2147483647#u32 hc
  norm_num at hb

theorem all_blocks_law_false :
    ¬ (∀ bytes, XRn_Join_Release.sampler.low_base_p_digits bytes =
      AspisR1Post25Sampler.sampler.low_base_p_digits bytes) := by
  intro h
  exact sampler_commutation_false (h block)

#print axioms emitted_low
#print axioms candidate_bound
#print axioms sampler_commutation_false
#print axioms all_blocks_law_false
end XRp_LowSamplerObstruction
