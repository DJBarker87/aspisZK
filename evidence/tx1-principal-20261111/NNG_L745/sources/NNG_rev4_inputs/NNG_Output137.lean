import NNG_Data137
import NNG_FinishAdapter137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Output137
open Aeneas Aeneas.Std Result


def verified {H : Type} (v : NMP_prepare.r1_semantic.Verified H) : NNG_verify_finish.r1_semantic.Verified H :=
  NNG_Transport.fromT11 (NMP_Transport.toT11 v)
def error (e : NMP_prepare.r1_wire.Error) : NNG_verify_finish.r1_wire.Error :=
  NNG_Transport.fromT13 (NMP_Transport.toT12 e)
def decode (a : NNG_Data137.Args) (env : RSL.Env) (r : NMP_Emitted.SemanticOut Unit) :
    Except LIB_VLib.library.WErr (RSL.Verified LIB_VLib.library) :=
  NNG_DProjection136.output (NNG_ProjectionFallback137.representation (NNG_Data137.fallback a env)) (NMP_ResultTransport.inner verified error r)

theorem verified_roundtrip (v : NNG_verify_finish.r1_semantic.Verified Unit) :
    verified (NMP_Transport.fromT11 (NNG_Transport.toT11 v))=v := by
  unfold verified
  rw [NMP_Transport.fromT11_inverse,NNG_Transport.toT11_inverse]
#print axioms verified_roundtrip

theorem error_roundtrip (e : NNG_verify_finish.r1_wire.Error) :
    error (NMP_Transport.fromT12 (NNG_Transport.toT13 e))=e := by
  unfold error
  rw [NMP_Transport.fromT12_inverse,NNG_Transport.toT13_inverse]
#print axioms error_roundtrip

theorem child_decode (a : NNG_Data137.Args) (env : RSL.Env)
    (child : RSL.TX1_136.Args LIB_VLib.library)
    (fallback : NNG_Data137.fallback a env=child.challenges.eta)
    (r : NNG_Emitted.Output Unit) :
    decode a env (NMP_ResultTransport.inner (fun v=>NMP_Transport.fromT11 (NNG_Transport.toT11 v))
      (fun e=>NMP_Transport.fromT12 (NNG_Transport.toT13 e)) r) =
      NNG_DProjection136.output (NNG_Representation136.project child) r := by
  unfold decode
  rw [fallback,NNG_ProjectionFallback137.representation_eq]
  cases r <;> simp only [NMP_ResultTransport.inner,verified_roundtrip,error_roundtrip]
#print axioms child_decode
end AspisR1.NNG_Output137
