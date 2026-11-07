import NNG_Data137
import NMP_Install131
import NMP_EmittedContext
import S1SemanticCodePublicTranscriptExactV1
import NNG_LIBDigest
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PublicSource137
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport
open NMP_ResultTransport (outer inner)
open AspisR1PublicPreparation (PreparedHashCode S1SemanticCode)

def digest (env : RSL.Env) : aspis_core.digest.Digest32 Unit :=
 ⟨(LIB_VCode.digest env).coremarkerCopyInst,(LIB_VCode.digest env).digest⟩

theorem digest_exact (env : RSL.Env) : NMP_Install131.digest (digest env)=LIB_VCode.digest env := rfl
#print axioms digest_exact

theorem key_native (key : Array U8 32#usize) : LIB_Env.nativeKey (LIB_Carriers.b32 key)=key := by
  apply LIB_Carriers.b32_injective
  exact LIB_Env.key_roundtrip _
#print axioms key_native

theorem value (env : RSL.Env) (pub : NMP_Emitted.Public) (root : Array U8 32#usize) :
    NMP_Install131.publicTranscript (digest env) pub () root =
      outer (inner fromT10 fromT12)
        (PreparedHashCode.run (S1SemanticCode.publicTranscript (LIB_VCode.digest env) (toT9 pub) () root)).2 := by
  unfold NMP_Install131.publicTranscript
  rw [digest_exact,PreparedHashCode.run_value,S1SemanticCode.publicTranscript_erasure]
#print axioms value
end AspisR1.NNG_PublicSource137
