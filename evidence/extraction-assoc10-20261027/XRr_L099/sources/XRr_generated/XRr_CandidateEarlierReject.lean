import XRr_CandidateReject
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_CandidateEarlierReject
theorem parse_error {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (physical proof : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
 (e : verifier.Error) (h : verifier.candidate.parse_shape proof=ok (.Err e)) :
 verifier.candidate.tx1 D pub physical proof compact.SPLIT hash obs=ok (.Err e) := by
 have test : ¬((compact.SPLIT != compact.SPLIT)=true) := by
   intro bad
   have ne : compact.SPLIT≠compact.SPLIT := by simpa only [bne_iff_ne] using bad
   exact ne rfl
 unfold verifier.candidate.tx1
 rw [if_neg test]
 simp only [h,bind_tc_ok,
   core.result.Result.Insts.CoreOpsTry.branch,
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
   core.convert.FromSame.from]
theorem scan_error {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (physical proof : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
 (shape : transport.Variant) (e : verifier.Error)
 (hp : verifier.candidate.parse_shape proof=ok (.Ok shape))
 (h : verifier.candidate.canonical_scan proof=ok (.Err e)) :
 verifier.candidate.tx1 D pub physical proof compact.SPLIT hash obs=ok (.Err e) := by
 have test : ¬((compact.SPLIT != compact.SPLIT)=true) := by
   intro bad
   have ne : compact.SPLIT≠compact.SPLIT := by simpa only [bne_iff_ne] using bad
   exact ne rfl
 unfold verifier.candidate.tx1
 rw [if_neg test]
 simp only [hp,h,bind_tc_ok,
   core.result.Result.Insts.CoreOpsTry.branch,
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
   core.convert.FromSame.from]
#print axioms parse_error
#print axioms scan_error
end XRr_CandidateEarlierReject
