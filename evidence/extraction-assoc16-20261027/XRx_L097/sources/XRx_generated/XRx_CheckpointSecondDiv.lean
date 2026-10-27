import XRr_CheckpointReject
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRx_CheckpointSecondDiv
/-- Complete the missing second-attempt divergence branch on the SAME model
checkpoint. This is not the OPEN LPm native checkpoint association. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (p : verifier.Prepared) (a : verifier.Accumulator) (proof physical : Slice U8)
 (hash : H) (proofHash : Array U8 32#usize)
 (first : XRn_Join_digest D hash [proof]=ok proofHash)
 (second : XRn_Join_digest D hash [physical]=.div) :
 verifier.checkpoint D p a proof physical hash=.div := by
 unfold verifier.checkpoint
 rw [first,bind_tc_ok,second,bind_tc_div]
 rfl
#print axioms source
end XRx_CheckpointSecondDiv
