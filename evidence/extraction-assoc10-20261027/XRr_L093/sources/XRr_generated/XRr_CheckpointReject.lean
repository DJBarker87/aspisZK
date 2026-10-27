import XRr_CheckpointAttempts
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_CheckpointReject
theorem first_fail {H : Type} (D : aspis_core.digest.Digest32 H)
 (p : verifier.Prepared) (a : verifier.Accumulator) (proof physical : Slice U8)
 (hash : H) (e : Error) (h : XRn_Join_digest D hash [proof]=.fail e) :
 verifier.checkpoint D p a proof physical hash=.fail e := by
 unfold verifier.checkpoint
 rw [h,bind_tc_fail]
theorem first_div {H : Type} (D : aspis_core.digest.Digest32 H)
 (p : verifier.Prepared) (a : verifier.Accumulator) (proof physical : Slice U8)
 (hash : H) (h : XRn_Join_digest D hash [proof]=.div) :
 verifier.checkpoint D p a proof physical hash=.div := by
 unfold verifier.checkpoint
 rw [h,bind_tc_div]
theorem second_fail {H : Type} (D : aspis_core.digest.Digest32 H)
 (p : verifier.Prepared) (a : verifier.Accumulator) (proof physical : Slice U8)
 (hash : H) (proofHash : Array U8 32#usize) (e : Error)
 (hp : XRn_Join_digest D hash [proof]=ok proofHash)
 (h : XRn_Join_digest D hash [physical]=.fail e) :
 verifier.checkpoint D p a proof physical hash=.fail e := by
 unfold verifier.checkpoint
 rw [hp,bind_tc_ok,h,bind_tc_fail]
#print axioms first_fail
#print axioms first_div
#print axioms second_fail
end XRr_CheckpointReject
