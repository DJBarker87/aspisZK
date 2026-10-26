import RPz7_F3K_RhoJoin
import RPz7_ExtractedSourceSemanticSampler
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_RhoMeaning
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge

def decode (q : aspis_core.field.QM31) : AspisV8R15.ExactTowerBase.QM31Exact :=
  ExtractedCurrentQM31Exact.decode
    (ExtractedQM31SamplerCarrier.toCurrent (SamplerTransport.toOld q))

theorem value (block : Array U8 32#usize) (out : aspis_core.field.QM31)
    (success : sampler.qm31_sample block=ok out) :
    LiteralOpeningView.eK (decode out)=SelectedTranscriptParams.params.σ 32 (decodeState block) := by
  simpa only [SelectedTranscriptParams.params_sigma,SelectedChallengeMap.sigma,
    show (32 : Nat)≠27 by decide,show ¬((32 : Nat)=28 ∨ 32=29 ∨ 32=30) by decide,
    show (32 : Nat)≠31 by decide,if_false,decode] using
    SourceSemanticSampler.sample_semChal block out success

#print axioms value
end AspisR1.F3L_RhoMeaning
end
