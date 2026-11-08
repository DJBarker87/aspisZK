import NNV_ObservedCut
import NNV_SemanticParse
import NNV_SemanticTranscript
import NNV_SemanticBegin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_SemanticPrefix
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NNH_Libraries
/-- All three source calls are linked at the SAME canonical returned prefix.
The semantic finish continuation is retained explicitly as the remaining cut. -/
theorem returned (pub : VL.Public) (bytes : Slice U8) (env : RSL.Env) (sem : RSL.Verified VL)
 (called : NNH_ObservedReturns.value ⟨pub,LIB_Carriers.bytes bytes⟩ env = .ok sem) :
 ∃ p : NNV_ObservedCut.Packet ⟨pub,LIB_Carriers.bytes bytes⟩ env sem,
 PrefixAdapter.parseAccepted bytes = .ok (.Ok (LIB_VCarriers.prefixRaw p.prefix_)) ∧
 r1_semantic.public_transcript (LIB_VCode.digest env) pub () (LIB_Env.nativeKey (VL.c1Root p.prefix_)) = .ok (.Ok p.initial) ∧
 r1_wire.begin (LIB_VCode.digest env) (LIB_VCarriers.prefixRaw p.prefix_) p.initial =
 .ok (.Ok (LIB_VCarriers.challengesRaw p.challenges),p.before) := by
 obtain ⟨p⟩ := NNV_ObservedCut.returned _ env sem called
 exact ⟨p,NNV_SemanticParse.returned bytes p.prefix_ env p.parsed,
  NNV_SemanticTranscript.returned _ env p.initial p.initialized,
  NNV_SemanticBegin.returned _ env p.challenges p.before p.begun⟩
#print axioms returned
end AspisR1.NNV_SemanticPrefix
end
