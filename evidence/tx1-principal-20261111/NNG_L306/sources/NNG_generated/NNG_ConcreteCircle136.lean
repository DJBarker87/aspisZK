import NNG_ConcreteGraph136
import NNG_LIBCircle
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ConcreteCircle136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport

theorem sourceObs (env : RSL.Env) (t : r1_wire.SemanticTranscript Unit) (r : r1_wire.ValidatedRecord) :
    (⟨NNG_Observed136.exit NNG_LIBCircle.project (NNG_ModelCircle.call (NNG_LIBDigest.digest env) t r),
      LIB_VCode.events env (NNG_ModelCircle.model (NNG_LIBDigest.digest env) t r).1⟩ :
        RSL.Obs (Except LIB_VCarriers.WErr (LIB_VCarriers.Point × LIB_VCarriers.Transcript))) =
      LIB_VCode.obs env LIB_VCircle.project (AspisR1PublicPreparation.PreparedHashCode.run
        (NJM_CircleCode.source (LIB_VCode.digest env) (toT10 t) (toT14 r))) := by
  unfold LIB_VCode.obs
  rw [NNG_ConcreteGraph136.mappedObs]
  have values := NNG_ConcreteGraph136.resultObs NNG_LIBCircle.project _ _
    (LIB_VCode.events env (NNG_ModelCircle.model (NNG_LIBDigest.digest env) t r).1)
    (NNG_LIBCircle.projected env t r)
  simpa only [NNG_ModelCircle.model,NNG_LIBDigest.installed] using values
#print axioms sourceObs

theorem circle0 (env : RSL.Env) (t : r1_wire.SemanticTranscript Unit) (r : r1_wire.ValidatedRecord)
    (frame : r.framed.val.length ≤ 3717) :
    RSL.Spec.map NNG_LIBCircle.project
      (NNG_Interpret136.call NNG_LIBEvents136.events "circle0" (t,r)
        (NNG_ModelCircle.call (NNG_LIBDigest.digest env) t r)) env =
      (LIB_VCircle.circle.run (toT10 t,toT14 r)) env := by
  apply NNG_EnvCallGraph136.effect_at LIB_VCircle.circle (toT10 t,toT14 r) frame
    NNG_LIBCircle.project NNG_LIBEvents136.events "circle0" (t,r) _ env
    (LIB_VCode.obs env LIB_VCircle.project (AspisR1PublicPreparation.PreparedHashCode.run
      (NJM_CircleCode.source (LIB_VCode.digest env) (toT10 t) (toT14 r))))
  · rw [NNG_LIBEvents136.circle0]
    exact sourceObs env t r
  · exact LIB_VCircle.law_exact (toT10 t,toT14 r) env
#print axioms circle0

theorem circle1 (env : RSL.Env) (t : r1_wire.SemanticTranscript Unit) (r : r1_wire.ValidatedRecord)
    (frame : r.framed.val.length ≤ 3717) :
    RSL.Spec.map NNG_LIBCircle.project
      (NNG_Interpret136.call NNG_LIBEvents136.events "circle1" (t,r)
        (NNG_ModelCircle.call (NNG_LIBDigest.digest env) t r)) env =
      (LIB_VCircle.circle.run (toT10 t,toT14 r)) env := by
  apply NNG_EnvCallGraph136.effect_at LIB_VCircle.circle (toT10 t,toT14 r) frame
    NNG_LIBCircle.project NNG_LIBEvents136.events "circle1" (t,r) _ env
    (LIB_VCode.obs env LIB_VCircle.project (AspisR1PublicPreparation.PreparedHashCode.run
      (NJM_CircleCode.source (LIB_VCode.digest env) (toT10 t) (toT14 r))))
  · rw [NNG_LIBEvents136.circle1]
    exact sourceObs env t r
  · exact LIB_VCircle.law_exact (toT10 t,toT14 r) env
#print axioms circle1
end AspisR1.NNG_ConcreteCircle136
