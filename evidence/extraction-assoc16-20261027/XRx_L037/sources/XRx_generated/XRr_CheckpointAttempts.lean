import XRr_CheckpointShape
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XRr_CheckpointAttempts
def label : Slice U8 :=
 ⟨[85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,58#u8,82#u8,49#u8,58#u8,
   99#u8,104#u8,101#u8,99#u8,107#u8,112#u8,111#u8,105#u8,110#u8,116#u8],by scalar_tac⟩
/-- The model's actual three digest cuts in source order on SAME bytes.
This is not the LPi native ordered-attempts law. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (proof physical : Slice U8) (hash : H) (saved : alloc.vec.Vec U8)
 (run : verifier.checkpoint D p a proof physical hash=ok saved) :
 ∃ (proofHash publicHash : Array U8 32#usize) (payload : Slice U8) (checksum : Array U8 32#usize),
 XRn_Join_digest D hash [proof]=ok proofHash ∧
 XRn_Join_digest D hash [physical]=ok publicHash ∧
 XRn_Join_digest D hash [label,payload]=ok checksum ∧
 saved.val=payload.val++checksum.val := by
 unfold verifier.checkpoint at run
 obtain ⟨proofHash,hproof,run⟩ := bind_success _ _ _ run
 obtain ⟨publicHash,hpublic,run⟩ := bind_success _ _ _ run
 obtain ⟨wide,_,run⟩ := bind_success _ _ _ run
 obtain ⟨payload,hpayload,run⟩ := bind_success _ _ _ run
 obtain ⟨checksum,hchecksum,run⟩ := bind_success _ _ _ run
 have hpayload' : XRn_Join_asSlice (XRr_CheckpointLayout.bytes p a proofHash publicHash wide)=ok payload := hpayload
 have hp := XRr_CheckpointLayout.slice _ payload hpayload'
 have hs := XRr_CheckpointFinalize.value (XRr_CheckpointLayout.bytes p a proofHash publicHash wide)
   checksum (if p.variant matches .S1 then 4840 else 1768) saved run
 refine ⟨proofHash,publicHash,payload,checksum,hproof,hpublic,hchecksum,?_⟩
 rw [hs,hp]
#print axioms source
end XRr_CheckpointAttempts
