import NNG_LIBEvents136
import LIB_VCircle
import NNG_EmittedCallGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBCircle
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport

def project : (core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error × r1_wire.SemanticTranscript Unit) →
    Except LIB_VCarriers.WErr (LIB_VCarriers.Point × LIB_VCarriers.Transcript)
 | (.Ok z,t) => .ok (toT2 z,toT10 t) | (.Err e,_) => .error (toT13 e)

theorem project_raise (reply : core.result.Result AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint
    AspisR1PublicPreparation.r1_wire.Error × LIB_VCarriers.Transcript) :
    project (NNG_ModelCircle.raiseReply reply) = LIB_VCircle.project reply := by
  rcases reply with ⟨r,t⟩
  cases r <;> simp only [NNG_ModelCircle.raiseReply,NMP_ResultTransport.inner,project,
    LIB_VCircle.project,fromT2_inverse,fromT10_inverse,fromT13_inverse]
#print axioms project_raise

theorem projected (env : RSL.Env) (t : r1_wire.SemanticTranscript Unit) (r : r1_wire.ValidatedRecord) :
    NNG_EmittedCallGraph.resultMap project (NNG_ModelCircle.call (NNG_LIBDigest.digest env) t r) =
      NNG_EmittedCallGraph.resultMap LIB_VCircle.project
        (AspisR1PublicPreparation.PreparedHashCode.run
          (NJM_CircleCode.source (LIB_VCode.digest env) (toT10 t) (toT14 r))).2 := by
  unfold NNG_ModelCircle.call NNG_ModelCircle.model
  rw [NNG_LIBDigest.installed]
  generalize (AspisR1PublicPreparation.PreparedHashCode.run
    (NJM_CircleCode.source (LIB_VCode.digest env) (toT10 t) (toT14 r))).2 = out
  cases out <;> simp only [NMP_ResultTransport.outer,NNG_EmittedCallGraph.resultMap,project_raise]
#print axioms projected
end AspisR1.NNG_LIBCircle
