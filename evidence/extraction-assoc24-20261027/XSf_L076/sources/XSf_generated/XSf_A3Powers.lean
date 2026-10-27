import XSf_Closed
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
noncomputable section
namespace XSf_A3Powers
open AspisR1ClaimPreparedBridge

/-- The observed powers array is identified with the one derived from the
SAME gamma call; neither the scratch nor its canonicality is assumed. -/
theorem observed_weights {H : Type} (D : C.D H) (before after : C.T H)
 (s : Slice U8) (gamma : C.E) (g : XSa_DotRun.Coeff)
 (hg : AspisR1PublicPreparation.PreparedModel.scalar XRo_Join_Installed.actual.sampling
   D before 27#u8 s true=ok (gamma,after))
 (hp : powersPublic 29#usize gamma=ok g) :
 XSa_DotRun.canonical g ∧ XRn_Join_Release.weights.powers 29#usize gamma=ok g := by
 obtain ⟨same,hr,ht,hc⟩ := XSa_PowersDimensions.twenty_nine gamma
   (XRy_PreparePowers.gamma_canonical D before after 27#u8 s gamma hg)
 have he : same=g := Result.ok.inj (ht.symm.trans hp)
 subst same
 exact ⟨hc,hr⟩

/-- Seven powers, their canonical cells, and the actual installed weighted
fold are all derived from one reached ordinary scalar, with no native P6 law. -/
theorem weighted {H : Type} (D : C.D H) (before after : C.T H)
 (payload : Slice U8) (kappa : C.E)
 (hk : AspisR1PublicPreparation.PreparedModel.scalar XRo_Join_Installed.actual.sampling
   D before 28#u8 payload false=ok (kappa,after))
 (parts : XRy_ClaimSumStep.Seven) (hc : XRy_ClaimSumStep.canonical parts) :
 ∃ k : XRy_ClaimSumStep.Seven,
 XRn_Join_powers kappa 7 XRy_Powers.one=ok k.val ∧
 ops.powers 7#usize (toClaimE kappa)=ok (arr toClaimE k) ∧
 XRy_ClaimSumStep.canonical k ∧
 ∃ out, XRy_WideMultiply.Canonical out ∧
 (k.val.zip parts.val).foldlM XSa_ClaimPairs.addTerm XRy_Powers.zero=ok out ∧
 AspisR1CurrentPreparedClaim.verifier.prepared_claim_sum (arr toClaimE k) (arr toClaimE parts)=ok (toClaimE out) := by
 obtain ⟨k,hr,ht,hkc⟩ := XSa_PowersDimensions.seven kappa
   (XSf_Reached.kappa D before after 28#u8 payload kappa hk)
 exact ⟨k,hr,ht,hkc,XSa_ClaimSumJoin.paired k parts hkc hc⟩

/-- SAME reached view, gamma, kappa and observed powers at the claim call. -/
theorem claim_at_call {H : Type} (D : C.D H) (sem : C.Sem H)
 (proof semantic y1 : Slice U8) (v : E.View)
 (view : _root_.verifier.candidate.wide_view proof semantic y1=ok (.Ok v))
 (t t1 t2 : C.T H) (gamma kappa : C.E) (bytes : Array U8 32#usize)
 (hg : AspisR1PublicPreparation.PreparedModel.scalar XRo_Join_Installed.actual.sampling
   D t 27#u8 v.y1 true=ok (gamma,t1))
 (hb : XRo_Join_Installed.actual.sampling.toBytes v.inactive=ok bytes)
 (hk : AspisR1PublicPreparation.PreparedModel.scalar XRo_Join_Installed.actual.sampling
   D t1 28#u8 (Array.to_slice bytes) false=ok (kappa,t2))
 (g : XSa_DotRun.Coeff) (hp : powersPublic 29#usize gamma=ok g) :
 XRo_Join_PreparedBoundaries.cachedClaim D sem v.y1 v.inactive g kappa =
 XRo_Join_Installed.actual.claim D sem v.y1 v.inactive g kappa := by
 have hc := (observed_weights D t t1 v.y1 gamma g hg hp).1
 exact XSa_CachedClaim.claim D sem v.y1 v.inactive kappa g
   (XSf_View.inactive proof semantic y1 v view)
   (XSf_Reached.kappa D t1 t2 28#u8 (Array.to_slice bytes) kappa hk) hc

#print axioms observed_weights
#print axioms weighted
#print axioms claim_at_call
end XSf_A3Powers
end
