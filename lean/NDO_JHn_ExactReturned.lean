import NDO_JHn_LiteReturnedIdentity
import NDO_JHn_ByteSHAProved
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHn_ExactReturned
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
/-- Unconditional byte identity for any successful candidate return. Tree
SHA equations are needed for acceptance, not for this implication. -/
theorem source (saved : alloc.vec.Vec U8)
    (returned : verifier.candidate.tx1 installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=ok (.Ok saved)) :
    saved.val=JFx_NativeBytes.checkpoint.val := by
  letI : JHn_ByteSHA := JHn_ByteSHAProved.source
  exact JHn_LiteReturnedIdentity.source saved returned
#print axioms source
end AspisR1.JHn_ExactReturned
end
