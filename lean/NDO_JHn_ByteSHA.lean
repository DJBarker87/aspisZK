import NDO_JHe_CurrentWriterImage
import NDO_JFn_HashBoundary
set_option autoImplicit false
namespace AspisR1
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
/-- Only the three concrete byte-digest equations used by the writer. Tree
realization belongs to batch acceptance, not to this writer identity proof. -/
class JHn_ByteSHA : Prop where
  proof : JFp_SHADigest.digest (flatten JFn_HashBoundary.proofParts)=decodeState JFo_AuthBytes.proofHash
  publicInput : JFp_SHADigest.digest (flatten JFn_HashBoundary.publicParts)=decodeState JFo_AuthBytes.publicHash
  checksum : JFp_SHADigest.digest (flatten JFn_HashBoundary.checksumParts)=decodeState JFo_AuthBytes.checksum
namespace JHn_ByteSHA
open Aeneas Aeneas.Std Result JHe_CurrentWriterImage
variable [sha : JHn_ByteSHA]
theorem proofCall (hp : Array U8 32#usize)
    (call : dictionary.digest () (AspisR1Stage2.WireTx2.singletonParts JFx_NativeBytes.proof)=ok hp) :
    hp=JFq_AuthBytes.proofHash := by
  change ok (encodeState (JFp_SHADigest.digest (flatten JFn_HashBoundary.proofParts)))=ok hp at call
  rw [JHn_ByteSHA.proof,array_roundtrip] at call
  exact (Result.ok.inj call).symm
#print axioms proofCall
theorem publicCall (hu : Array U8 32#usize)
    (call : dictionary.digest () (AspisR1Stage2.WireTx2.singletonParts JFx_NativeBytes.publicInput)=ok hu) :
    hu=JFq_AuthBytes.publicHash := by
  change ok (encodeState (JFp_SHADigest.digest (flatten JFn_HashBoundary.publicParts)))=ok hu at call
  rw [JHn_ByteSHA.publicInput,array_roundtrip] at call
  exact (Result.ok.inj call).symm
#print axioms publicCall
end JHn_ByteSHA
end AspisR1
