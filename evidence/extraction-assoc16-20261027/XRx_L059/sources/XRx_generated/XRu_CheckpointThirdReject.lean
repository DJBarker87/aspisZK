import XRu_CheckpointTail
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRu_CheckpointThirdReject
theorem fail {H : Type} (D : aspis_core.digest.Digest32 H)
 (p : verifier.Prepared) (a : verifier.Accumulator) (proof physical : Slice U8) (hash : H)
 (proofHash publicHash : Array U8 32#usize) (wide : List (Array U8 32#usize)) (payload : Slice U8) (e : Error)
 (hp : XRn_Join_digest D hash [proof]=ok proofHash)
 (hu : XRn_Join_digest D hash [physical]=ok publicHash)
 (hw : XRu_CheckpointTail.wides p a=ok wide)
 (hs : XRn_Join_asSlice (XRr_CheckpointLayout.bytes p a proofHash publicHash wide)=ok payload)
 (rejected : XRn_Join_digest D hash [XRr_CheckpointAttempts.label,payload]=.fail e) :
 verifier.checkpoint D p a proof physical hash=.fail e := by
 rw [XRu_CheckpointTail.source D p a proof physical hash proofHash publicHash wide payload hp hu hw hs,rejected]
 rfl
#print axioms fail
theorem div {H : Type} (D : aspis_core.digest.Digest32 H)
 (p : verifier.Prepared) (a : verifier.Accumulator) (proof physical : Slice U8) (hash : H)
 (proofHash publicHash : Array U8 32#usize) (wide : List (Array U8 32#usize)) (payload : Slice U8)
 (hp : XRn_Join_digest D hash [proof]=ok proofHash)
 (hu : XRn_Join_digest D hash [physical]=ok publicHash)
 (hw : XRu_CheckpointTail.wides p a=ok wide)
 (hs : XRn_Join_asSlice (XRr_CheckpointLayout.bytes p a proofHash publicHash wide)=ok payload)
 (rejected : XRn_Join_digest D hash [XRr_CheckpointAttempts.label,payload]=.div) :
 verifier.checkpoint D p a proof physical hash=.div := by
 rw [XRu_CheckpointTail.source D p a proof physical hash proofHash publicHash wide payload hp hu hw hs,rejected]
 rfl
#print axioms div
end XRu_CheckpointThirdReject
