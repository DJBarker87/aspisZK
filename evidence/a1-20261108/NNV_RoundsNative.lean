import NNV_FinishRounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_RoundsNative
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

theorem returned (p : Prefix) (t : Transcript) (env : RSL.Env)
 (r : QM31 × Alpha × Transcript)
 (called : LIB_VLib.semanticRoundsValue (p,t) env = .ok r) :
 RoundModel.rounds NJM_RoundJoin.R (LIB_VCode.digest env) (prefixRaw p) t =
 .ok (.Ok (LIB_VScalarCarriers.toRaw r.1,alphaRaw r.2.1,r.2.2)) := by
 rw [←S1SemanticCode.rounds_erasure]
 exact NNV_FinishRounds.returned p t env r called
#print axioms returned
end AspisR1.NNV_RoundsNative
end
