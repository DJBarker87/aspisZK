import RPz7_CurrentPreparedConcreteBoundaries
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim
local notation "QRaw" => AspisR1EbyKPushDecodedProductUpdate.QRaw

def ConcreteClaimRun {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch : Array PE 29#usize) : Prop :=
  ClaimPowers.powers 29#usize (toClaimE out.gamma)=ok (mapArray toClaimE scratch) ∧
  verifier.prepared_claim (AspisR1S5ClaimDotConcreteAdapter.concreteOps QRaw)
    (toClaimDigest D) (toClaimSem sem) v.y1 (toClaimE v.inactive)
    (mapArray toClaimE scratch) (toClaimE out.kappa)=ok (.Ok (toClaimE out.claim))

theorem afterQueries_concrete_run {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (gamma kappa : PE)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch : Array PE 29#usize)
    {alpha : Array PE 2#usize} {row : U8} {before : AspisR1PublicPreparation.transcript.Transcript H}
    (h : AspisR1PublicPreparation.PreparedScratchReachability.AfterQueries
      (concreteBoundaries sampling) D sem v gamma kappa alpha row before out scratch) :
    out.gamma=gamma ∧ out.kappa=kappa ∧ ConcreteClaimRun D sem v out scratch := by
  obtain ⟨queries,afterQueries,last,rho,claim,hq,hrho,hp,hc,he⟩ := h
  have hp1 := powersPublic_success gamma scratch hp
  have hc1 := claimPublic_success D sem v.y1 v.inactive kappa claim scratch hc
  subst out
  exact ⟨rfl,rfl,hp1,hc1⟩

theorem tail_concrete_run {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (gamma kappa alpha0 : PE)
    (before : AspisR1PublicPreparation.transcript.Transcript H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch : Array PE 29#usize)
    (h : AspisR1PublicPreparation.PreparedScratchReachability.Tail
      (concreteBoundaries sampling) D sem v gamma kappa alpha0 before out scratch) :
    out.gamma=gamma ∧ out.kappa=kappa ∧ ConcreteClaimRun D sem v out scratch := by
  cases h with
  | single hf ha => exact afterQueries_concrete_run sampling D sem v gamma kappa out scratch ha
  | double hf root b1 b2 a1 ta hr hb1 hb2 hal ha =>
    exact afterQueries_concrete_run sampling D sem v gamma kappa out scratch ha

theorem prepared_success_concrete_claim {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (h : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (concreteBoundaries sampling) D sem v hash scratchIn=ok (.Ok out,scratch)) :
    ConcreteClaimRun D sem v out scratch := by
  obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,hseed,hg,hb,hk,ha,ht⟩ :=
    AspisR1PublicPreparation.PreparedScratchReachability.prepare_success
      (concreteBoundaries sampling) D sem v hash out scratch scratchIn h
  exact (tail_concrete_run sampling D sem v gamma kappa alpha0 t3 out scratch ht).2.2

#print axioms afterQueries_concrete_run
#print axioms tail_concrete_run
#print axioms prepared_success_concrete_claim
end AspisR1ClaimPreparedBridge
