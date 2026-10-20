import PowersP6GeneratedTotalV1
import CurrentPreparedConcreteBoundaries
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PreparedSourcePowersBoundariesV1
open AspisR1ClaimPreparedBridge AspisR1CurrentPreparedClaim
open AspisR1PowersP6GeneratedErasureV1 AspisR1PowersP6GeneratedTotalV1
open AspisR1PublicPreparation.PreparedScratchReachability

def sourcePowersPublic (N : Usize) (x : PE) : Result (Array PE N) := do
  let values ← sourceArrayPowers N (toClaimE x)
  ok (mapArray fromClaimE values)

theorem sourcePowersPublic_eq (N : Usize) (x : PE)
    (hx : Concrete.Canonical (toClaimE x)) :
    sourcePowersPublic N x=powersPublic N x := by
  unfold sourcePowersPublic powersPublic
  rw [sourceArrayPowers_eq_claimPowers N (toClaimE x) hx]

def sourceClaimPublic {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (y1 : Slice U8)
    (inactive : PE) (g : Array PE 29#usize) (kappa : PE) :
    Result (core.result.Result PE AspisR1PublicPreparation.verifier.Error) := do
  let r ← verifier.prepared_claim
    (withSourceArrayPowers (AspisR1S5ClaimDotConcreteAdapter.concreteOps
      AspisR1EbyKPushDecodedProductUpdate.QRaw))
    (toClaimDigest D) (toClaimSem sem) y1 (toClaimE inactive)
    (mapArray toClaimE g) (toClaimE kappa)
  ok (match r with
    | .Ok x => .Ok (fromClaimE x)
    | .Err e => .Err (fromClaimError e))

theorem sourceClaimPublic_eq {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (y1 : Slice U8)
    (inactive : PE) (g : Array PE 29#usize) (kappa : PE)
    (hk : Concrete.Canonical (toClaimE kappa)) :
    sourceClaimPublic D sem y1 inactive g kappa=claimPublic D sem y1 inactive g kappa := by
  have hc := prepared_claim_sourceArray_eq
    (AspisR1S5ClaimDotConcreteAdapter.concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw)
    (toClaimDigest D) (toClaimSem sem) y1 (toClaimE inactive)
    (mapArray toClaimE g) (toClaimE kappa) hk
  unfold sourceClaimPublic claimPublic
  rw [hc]
  rfl

def sourceBoundaries (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries) :
    AspisR1PublicPreparation.PreparedScratchModel.Boundaries :=
  {sampling := sampling,powers := sourcePowersPublic,claim := sourceClaimPublic}

theorem sourceAfterQueries_transport {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (gamma kappa : PE)
    (alpha : Array PE 2#usize) (row : U8)
    (before : AspisR1PublicPreparation.transcript.Transcript H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch : Array PE 29#usize)
    (hg : Concrete.Canonical (toClaimE gamma)) (hk : Concrete.Canonical (toClaimE kappa))
    (h : AfterQueries (sourceBoundaries sampling) D sem v gamma kappa alpha row before out scratch) :
    AfterQueries (concreteBoundaries sampling) D sem v gamma kappa alpha row before out scratch := by
  rcases h with ⟨queries,afterQueries,last,rho,claim,hq,hr,hp,hc,ho⟩
  refine ⟨queries,afterQueries,last,rho,claim,hq,hr,?_,?_,ho⟩
  · change sourcePowersPublic 29#usize gamma=ok scratch at hp
    rw [sourcePowersPublic_eq 29#usize gamma hg] at hp
    exact hp
  · change sourceClaimPublic D sem v.y1 v.inactive scratch kappa=ok (.Ok claim) at hc
    rw [sourceClaimPublic_eq D sem v.y1 v.inactive scratch kappa hk] at hc
    exact hc

theorem sourceTail_transport {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (gamma kappa alpha0 : PE)
    (before : AspisR1PublicPreparation.transcript.Transcript H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch : Array PE 29#usize)
    (hg : Concrete.Canonical (toClaimE gamma)) (hk : Concrete.Canonical (toClaimE kappa))
    (h : Tail (sourceBoundaries sampling) D sem v gamma kappa alpha0 before out scratch) :
    Tail (concreteBoundaries sampling) D sem v gamma kappa alpha0 before out scratch := by
  cases h with
  | single hfolds tail =>
    exact .single hfolds (sourceAfterQueries_transport sampling D sem v gamma kappa _ _ _ out scratch hg hk tail)
  | double hfolds root bytes1 bytes2 alpha1 afterAlpha hroot hbytes1 hbytes2 halpha1 tail =>
    exact .double hfolds root bytes1 bytes2 alpha1 afterAlpha hroot hbytes1 hbytes2 halpha1
      (sourceAfterQueries_transport sampling D sem v gamma kappa _ _ _ out scratch hg hk tail)

#print axioms sourcePowersPublic_eq
#print axioms sourceClaimPublic_eq
#print axioms sourceAfterQueries_transport
#print axioms sourceTail_transport
end AspisR1PreparedSourcePowersBoundariesV1
