import XRr_CheckpointFinalize
import XRk_ResultTools
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XRr_CheckpointShape
/-- Literal slice model, without normalizing a checkpoint numeral/list. -/
theorem slice (bs : List U8) (out : Slice U8) (h : XRn_Join_asSlice bs=ok out) : out.val=bs := by
 unfold XRn_Join_asSlice at h
 split at h
 · exact (congrArg Subtype.val (Result.ok.inj h)).symm
 · cases h
/-- A successful opaque model return retains its size guard. This supplies
no native leaf certificate and does not promote the model to shipped Rust. -/
theorem size {H : Type} (D : aspis_core.digest.Digest32 H)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (proof physical : Slice U8) (hash : H) (saved : alloc.vec.Vec U8)
 (run : verifier.checkpoint D p a proof physical hash=ok saved) :
 saved.val.length=(if p.variant matches .S1 then 4840 else 1768) := by
 unfold verifier.checkpoint at run
 obtain ⟨proofHash,_,run⟩ := bind_success _ _ _ run
 obtain ⟨publicHash,_,run⟩ := bind_success _ _ _ run
 obtain ⟨wide,_,run⟩ := bind_success _ _ _ run
 obtain ⟨payload,_,run⟩ := bind_success _ _ _ run
 obtain ⟨checksum,_,run⟩ := bind_success _ _ _ run
 exact XRr_CheckpointFinalize.length
   (XRr_CheckpointLayout.bytes p a proofHash publicHash wide) checksum
   (if p.variant matches .S1 then 4840 else 1768) saved run
#print axioms slice
#print axioms size
end XRr_CheckpointShape
