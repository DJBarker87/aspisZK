import R1Z.PV_B2_LowDigits
import R1Z.PV_B2_CheckedDigits
import IndexedCandidateOrdinarySampleBridgeV3
set_option autoImplicit false
noncomputable section
namespace PV_B2_RankDigits
open Aeneas Aeneas.Std Result

/-- Complete Result and exact numeric digits of the applied copy's division
recurrence, for every256-bit block. No success premise is assumed. -/
theorem source (block : Array U8 32#usize) :
    ∃ digits : Array U32 8#usize, ∃ quotient : U32,
      PV_B2_Sampler.host_sampler.low_base_p_digits block = ok (digits,quotient) ∧
      AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values digits =
        AspisR1.SamplerNatModel.ordinaryDigits (AspisR1.SourceSamplerByteRank.rank block) ∧
      AspisR1.SamplerAddDigits.digitsValue AspisR1.SamplerMachineBounds.P
        (AspisR1.SamplerNatModel.ordinaryDigits (AspisR1.SourceSamplerByteRank.rank block)) =
        AspisR1.SourceSamplerByteRank.rank block % AspisR1.SamplerMachineBounds.P^8 := by
  obtain ⟨outRank,digits,q,hlow,_,hvalues,hresidue,_⟩ :=
    AspisR1.ExtractedQM31SamplerIndexedOrdinaryBridgeV1.ordinary_sample_candidate block
  refine ⟨digits,q,?_,hvalues,hresidue⟩
  rw [PV_B2_LowDigits.source,R1Z.PV_B2_CheckedDigits.digits]
  exact hlow
#print axioms source
end PV_B2_RankDigits
