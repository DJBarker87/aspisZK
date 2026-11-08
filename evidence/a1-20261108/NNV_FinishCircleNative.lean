import NNV_FinishCircle
import S1SemanticCodeCircleValidatedExactV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_FinishCircleNative
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

theorem returned (B : FinishModel.Boundaries) (t : Transcript) (r : Record)
 (env : RSL.Env) (z : Point) (after : Transcript)
 (called : LIB_VLib.circleValue (t,r) env = .ok (z,after)) :
 FinishModel.circle_validated (F3M_CircleSource.install B) (LIB_VCode.digest env) t r = .ok (.Ok z,after) := by
 rw [←S1SemanticCode.circleValidated_erasure]
 exact (congrArg Prod.snd (NJM_CircleCode.original B (LIB_VCode.digest env) t r)).trans
  (NNV_FinishCircle.returned t r env z after called)
#print axioms returned
end AspisR1.NNV_FinishCircleNative
end
