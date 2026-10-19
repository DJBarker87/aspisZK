import ExtractedSourceSemanticSampler
import RawActualAnnotatedPolynomialRun

/-! Match the source sampler's retained carrier transport to the decoder used
by the actual-round sumcheck chain, before identifying challenge lists. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawSourceChallengeCarrier
open AspisR1
open AspisV8R15.ExactTowerBase
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun

 theorem source_carrier_eq_round_carrier (q : MainQM) :
    algebraMap QM31Exact AspisWideTower.WideExact
      (ExtractedCurrentQM31Exact.decode
        (ExtractedQM31SamplerCarrier.toCurrent (SamplerTransport.toOld q))) =
      algebraMap E AspisWideTower.WideExact (DecodeMain q) := by
  rfl

#print axioms source_carrier_eq_round_carrier
end AspisR1PublicPreparation.RawSourceChallengeCarrier
end
