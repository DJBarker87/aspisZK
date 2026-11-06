import NLB_EnteredCommonTransport
import NLP_TransportDomain
set_option autoImplicit false
noncomputable section
namespace NLP_EnteredTransport
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved NLB_ErrorTransport
/-- Corrected auxiliary transport domain: C04's folded root is THAT proof
projection, not an arbitrary extra root argument. The old NLB merkleReply
premise is too broad to instantiate verbatim with NLN's own-input domain. -/
abbrev Domain := NLP_TransportDomain.Domain
theorem source (wr rr : NP6_StdModel.Reservation) (nativeMerkle modelMerkle : Merkle) (finish : Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (child : ∀ pr p root,Domain wr d ck proof pub hash pr p root →
  ReplyRel (nativeMerkle d pr p root 1#usize hash) (modelMerkle d pr p root 1#usize hash)) :
 observeCommon (run wr rr nativeMerkle finish d pub proof ck hash none)=
 observeCommon (run wr rr modelMerkle finish d pub proof ck hash none) := by
 unfold NJU_CommonObserved.run
 simp only [NKO_Offsets.folded,NKO_Offsets.round1,NKE_Entered.lift_ok]
 repeat' first
 | (apply observe_bind_entered; intro value entered)
 | (apply merkle_question)
 | (apply child)
 | (apply NLP_TransportDomain.at_branch <;> assumption)
 | (apply NKO_Branch.continued <;> assumption)
 | (apply split_start; assumption)
 | (apply NKE_ResumeWidth.returned; apply NKO_Branch.continued <;> assumption)
 | (fail_if_no_progress dsimp only [NJU_Log.prod_cases])
 | split
 | (intro u)
 | rfl
set_option pp.proofs false
#print Domain
#print source
#print axioms source
end NLP_EnteredTransport
