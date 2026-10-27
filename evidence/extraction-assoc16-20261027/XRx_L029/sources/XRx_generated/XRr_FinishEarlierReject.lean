import XRr_ObservedReject
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_FinishEarlierReject
theorem rounds_error {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (p : r1_wire.Prefix) (s : r1_wire.SemanticTranscript H)
 (c : aspis_core.state_only_prefix.r0.Challenges)
 (obs : Option (verifier.Phase → Result Unit)) (e : r1_wire.Error)
 (h : r1_semantic.semantic_rounds D p s=ok (.Err e)) :
 r1_semantic.verify_finish D pub p s c obs=ok (.Err e) := by
 unfold r1_semantic.verify_finish
 rw [h,bind_tc_ok]
 rfl

theorem rounds_fail {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (p : r1_wire.Prefix) (s : r1_wire.SemanticTranscript H)
 (c : aspis_core.state_only_prefix.r0.Challenges)
 (obs : Option (verifier.Phase → Result Unit)) (e : Error)
 (h : r1_semantic.semantic_rounds D p s=.fail e) :
 r1_semantic.verify_finish D pub p s c obs=.fail e := by
 unfold r1_semantic.verify_finish
 rw [h,bind_tc_fail]

theorem rounds_div {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (p : r1_wire.Prefix) (s : r1_wire.SemanticTranscript H)
 (c : aspis_core.state_only_prefix.r0.Challenges)
 (obs : Option (verifier.Phase → Result Unit))
 (h : r1_semantic.semantic_rounds D p s=.div) :
 r1_semantic.verify_finish D pub p s c obs=.div := by
 unfold r1_semantic.verify_finish
 rw [h,bind_tc_div]
#print axioms rounds_error
#print axioms rounds_fail
#print axioms rounds_div
end XRr_FinishEarlierReject
