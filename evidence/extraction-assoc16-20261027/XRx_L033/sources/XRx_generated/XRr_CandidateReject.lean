import XRr_CandidateCuts
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_CandidateReject
theorem wrong_split {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (physical proof : Slice U8) (split : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) (wrong : split≠compact.SPLIT) :
 verifier.candidate.tx1 D pub physical proof split hash obs=ok (.Err .Parse) := by
 unfold verifier.candidate.tx1
 have test : (split != compact.SPLIT)=true := by simpa only [bne_iff_ne] using wrong
 rw [if_pos test]
/-- Actual first rejection, without any separately assumed parsing or child run. -/
theorem zero_split {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (physical proof : Slice U8) (hash : H) :
 verifier.candidate.tx1 D pub physical proof 0#usize hash none=ok (.Err .Parse) := by
 apply wrong_split
 unfold compact.SPLIT
 scalar_tac
#print axioms wrong_split
#print axioms zero_split
end XRr_CandidateReject
