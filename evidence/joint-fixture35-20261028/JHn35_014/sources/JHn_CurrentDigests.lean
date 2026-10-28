import JHe_CurrentWriterImage
import JHh_SHARealization
set_option autoImplicit false
namespace AspisR1.JHn_CurrentDigests
open Aeneas Aeneas.Std Result
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open JHe_CurrentWriterImage
variable [sha : JHh_SHARealization]
/-- Identify an actual proof digest call, using only its concrete SHA equation. -/
theorem proof (hp : Array U8 32#usize)
    (call : dictionary.digest () (AspisR1Stage2.WireTx2.singletonParts JFx_NativeBytes.proof)=ok hp) :
    hp=JFq_AuthBytes.proofHash := by
  change ok (encodeState (JFp_SHADigest.digest (flatten JFn_HashBoundary.proofParts)))=ok hp at call
  rw [JHh_SHARealization.proof,array_roundtrip] at call
  exact (Result.ok.inj call).symm
#print axioms proof
/-- Identify the actual physical-public digest call. -/
theorem publicInput (hu : Array U8 32#usize)
    (call : dictionary.digest () (AspisR1Stage2.WireTx2.singletonParts JFx_NativeBytes.publicInput)=ok hu) :
    hu=JFq_AuthBytes.publicHash := by
  change ok (encodeState (JFp_SHADigest.digest (flatten JFn_HashBoundary.publicParts)))=ok hu at call
  rw [JHh_SHARealization.publicInput,array_roundtrip] at call
  exact (Result.ok.inj call).symm
#print axioms publicInput
end AspisR1.JHn_CurrentDigests
