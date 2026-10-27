import XRr_ObservedReject
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_ObservedEarlierReject
theorem public_error {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
 (p : r1_wire.Prefix) (e : r1_wire.Error)
 (hp : r1_wire.Prefix.parse bytes=ok (.Ok p))
 (he : r1_semantic.public_transcript D pub hash p.c1_root=ok (.Err e)) :
 r1_semantic.verify_observed D pub bytes hash obs=ok (.Err e) := by
 simp only [r1_semantic.verify_observed,hp,bind_tc_ok,
   core.result.Result.Insts.CoreOpsTry.branch,r1_semantic.mark,he,
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
   core.convert.FromSame.from]

theorem begin_error {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
 (p : r1_wire.Prefix) (initial after : r1_wire.SemanticTranscript H) (e : r1_wire.Error)
 (hp : r1_wire.Prefix.parse bytes=ok (.Ok p))
 (hi : r1_semantic.public_transcript D pub hash p.c1_root=ok (.Ok initial))
 (hb : r1_wire.begin D p initial=ok (.Err e,after)) :
 r1_semantic.verify_observed D pub bytes hash obs=ok (.Err e) := by
 simp only [r1_semantic.verify_observed,hp,bind_tc_ok,
   core.result.Result.Insts.CoreOpsTry.branch,r1_semantic.mark,hi,hb,
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
   core.convert.FromSame.from]

theorem begin_fail {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
 (p : r1_wire.Prefix) (initial : r1_wire.SemanticTranscript H) (e : Error)
 (hp : r1_wire.Prefix.parse bytes=ok (.Ok p))
 (hi : r1_semantic.public_transcript D pub hash p.c1_root=ok (.Ok initial))
 (hb : r1_wire.begin D p initial=.fail e) :
 r1_semantic.verify_observed D pub bytes hash obs=.fail e := by
 simp only [r1_semantic.verify_observed,hp,bind_tc_ok,
   core.result.Result.Insts.CoreOpsTry.branch,r1_semantic.mark,hi,hb,bind_tc_fail]
#print axioms public_error
#print axioms begin_error
#print axioms begin_fail
end XRr_ObservedEarlierReject
