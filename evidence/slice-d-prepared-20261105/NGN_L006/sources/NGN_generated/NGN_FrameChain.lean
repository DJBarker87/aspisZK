import NGN_Opening
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGN_FrameChain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedScratchReachability NFW_PreparedControl NGN_Opening NGN_Cuts

/-- Each premise is a named child-call observation, never a whole-function
success or output equality. These model edges keep the SAME variables. Native
realization of a child observation remains a separately listed obligation. -/
theorem gamma_kappa (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (v : verifier.View) (start after : transcript.Transcript H) (gamma : PE)
 (child : PreparedModel.scalar B.sampling D start 27#u8 v.y1 true=ok (gamma,after)) :
 gammaCut B D v start=kappaCut B D v gamma after := by
 simp only [gammaCut,child,bind_tc_ok]
 rfl

theorem kappa_alpha (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (v : verifier.View) (before after : transcript.Transcript H) (gamma kappa : PE)
 (bytes : Array U8 32#usize)
 (serialize : B.sampling.toBytes v.inactive=ok bytes)
 (child : PreparedModel.scalar B.sampling D before 28#u8 (Array.to_slice bytes) false=ok (kappa,after)) :
 kappaCut B D v gamma before=alphaCut B D v gamma kappa after := by
 simp only [kappaCut,serialize,child,lift,bind_tc_ok]
 rfl

theorem alpha_fold (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (v : verifier.View) (before after : transcript.Transcript H) (gamma kappa alpha0 : PE)
 (child : PreparedModel.scalar B.sampling D before 29#u8 v.round0 false=ok (alpha0,after)) :
 alphaCut B D v gamma kappa before=foldCut B D v gamma kappa alpha0 after := by
 simp only [alphaCut,child,bind_tc_ok]
 rfl

theorem query_rho (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (old : Scratch) (o : Opening H)
 (queries : Array U32 22#usize) (after : transcript.Transcript H)
 (child : B.sampling.queries D o.transcript o.row v.final_message=ok (.Ok queries,after)) :
 queryCut B D sem v old o=rhoCut B D sem v o queries after := by
 simp only [queryCut,child,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
 rfl

theorem rho_powers (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (o : Opening H)
 (queries : Array U32 22#usize) (before after : transcript.Transcript H) (row : U8)
 (rho : aspis_core.field.QM31) (increment : (o.row+1#u8 : Result U8)=ok row)
 (child : PreparedModel.scalar_k B.sampling D before row emptyPayload=ok (rho,after)) :
 rhoCut B D sem v o queries before=powersCut B D sem v o queries rho after := by
 simp only [rhoCut,increment,lift,bind_tc_ok]
 change (do let (r,t) ← PreparedModel.scalar_k B.sampling D before row emptyPayload
            powersCut B D sem v o queries r t)=_
 rw [child,bind_tc_ok]

theorem powers_claim (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (o : Opening H)
 (queries : Array U32 22#usize) (rho : aspis_core.field.QM31) (last : transcript.Transcript H)
 (g : Scratch) (child : B.powers 29#usize o.gamma=ok g) :
 powersCut B D sem v o queries rho last=claimCut B D sem v g o queries rho last := by
 simp only [powersCut,child,bind_tc_ok]

/-- Query failure returns the incoming scratch; there is no invented powers
result and no claim invocation on this branch. -/
theorem query_exit (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (old : Scratch) (o : Opening H)
 (e : verifier.Error) (after : transcript.Transcript H)
 (child : B.sampling.queries D o.transcript o.row v.final_message=ok (.Err e,after)) :
 queryCut B D sem v old o=ok (.Err e,old) := by
 rw [← NGN_Cuts.continuation]
 exact NFW_PreparedResults.query_error B D sem v old o e after child

#print axioms gamma_kappa
#print axioms kappa_alpha
#print axioms alpha_fold
#print axioms query_rho
#print axioms rho_powers
#print axioms powers_claim
#print axioms query_exit
end AspisR1.NGN_FrameChain
