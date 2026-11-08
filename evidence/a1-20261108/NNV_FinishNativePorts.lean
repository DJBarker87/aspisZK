import NNV_FinishRounds
import NNV_FinishCircle
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_FinishNativePorts
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

theorem rounds (p : Prefix) (t : Transcript) (env : RSL.Env)
 (r : QM31 × Alpha × Transcript)
 (called : LIB_VLib.semanticRoundsValue (p,t) env = .ok r) :
 RoundModel.rounds NJM_RoundJoin.R (LIB_VCode.digest env) (prefixRaw p) t =
 .ok (.Ok (LIB_VScalarCarriers.toRaw r.1,alphaRaw r.2.1,r.2.2)) :=
 (S1SemanticCode.rounds_erasure _ _ _ _).symm.trans
  ((PreparedHashCode.run_value _).symm.trans (NNV_FinishRounds.returned p t env r called))

theorem circle (B : FinishModel.Boundaries) (t : Transcript) (r : Record)
 (env : RSL.Env) (z : Point) (after : Transcript)
 (called : LIB_VLib.circleValue (t,r) env = .ok (z,after)) :
 FinishModel.circle_validated (F3M_CircleSource.install B) (LIB_VCode.digest env) t r = .ok (.Ok z,after) :=
 (S1SemanticCode.circleValidated_erasure _ _ _ _).symm.trans
  ((PreparedHashCode.run_value _).symm.trans
   ((congrArg Prod.snd (NJM_CircleCode.original B (LIB_VCode.digest env) t r)).trans
    (NNV_FinishCircle.returned t r env z after called)))
#print axioms rounds
#print axioms circle
end AspisR1.NNV_FinishNativePorts
end
