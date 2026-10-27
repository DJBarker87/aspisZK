import R1Z.PV_B2_C_NativeGammaCarrier
set_option autoImplicit false
namespace PV_B2_D_NativeOrdinaryCarrier
open Aeneas Aeneas.Std Result PV_B2_C_NativeGammaCarrier

/-- Complete native-carrier presentation of the normalized ordinary source.
This does not identify the frozen sampler or install operation250. -/
theorem source (block : Array U8 32#usize) :
    ∃ digits : Array U32 8#usize,
      mapResult toNative (PV_B2_C_Sampler.host_sampler.ordinary_sample block) =
        ok (toNative (PV_B2_C_ArrayDigits.raw digits)) ∧
      AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values digits =
        AspisR1.SamplerNatModel.ordinaryDigits (AspisR1.SourceSamplerByteRank.rank block) := by
  obtain ⟨digits,hr,hv⟩ := PV_B2_C_ordinary_sample.op250_source block
  refine ⟨digits,?_,hv⟩
  rw [hr]
  rfl
#print axioms source
end PV_B2_D_NativeOrdinaryCarrier
