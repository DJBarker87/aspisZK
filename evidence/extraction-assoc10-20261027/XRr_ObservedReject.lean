import XRn_Join_Funs
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_ObservedReject
/-- The first parser error issues neither public initialization nor begin. -/
theorem parse_error {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
 (e : r1_wire.Error) (h : r1_wire.Prefix.parse bytes=ok (.Err e)) :
 r1_semantic.verify_observed D pub bytes hash obs=ok (.Err e) := by
 unfold r1_semantic.verify_observed
 rw [h,bind_tc_ok]
 rfl

theorem parse_fail {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
 (e : Error) (h : r1_wire.Prefix.parse bytes=.fail e) :
 r1_semantic.verify_observed D pub bytes hash obs=.fail e := by
 unfold r1_semantic.verify_observed
 rw [h,bind_tc_fail]

theorem parse_div {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
 (h : r1_wire.Prefix.parse bytes=.div) :
 r1_semantic.verify_observed D pub bytes hash obs=.div := by
 unfold r1_semantic.verify_observed
 rw [h,bind_tc_div]
#print axioms parse_error
#print axioms parse_fail
#print axioms parse_div
end XRr_ObservedReject
