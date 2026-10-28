import NBA_Installed
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBA_Scalars
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim.Concrete
open AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1CurrentCaller.OriginalSerializerInstallation

def base : PreparedModel.Boundaries :=
 PreparedFromQmSourceBridge.withSourceFromQm
   (CurrentQueryRho.withConcreteQueries (withOriginalSerializer closedSampling)
     AspisS1M31Embedding.Total.embed)

theorem sampling : NBA_Installed.actual.sampling=withCandidateSamplers base := rfl

/-- SAME producing scalar call; no gamma value/bounds are assumed. -/
theorem gamma {H : Type} (D : aspis_core.Digest32 H)
    (before after : transcript.Transcript H) (row : U8) (payload : Slice U8) (out : PE)
    (call : PreparedModel.scalar NBA_Installed.actual.sampling D before row payload true=ok (out,after)) :
    Canonical (toClaimE out) := by
  rw [sampling] at call
  exact scalar_candidate_gamma_canonical
    (AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary base)
    D before after row payload out call

/-- Every ordinary scalar, including kappa and both fold challenges. -/
theorem ordinary {H : Type} (D : aspis_core.Digest32 H)
    (before after : transcript.Transcript H) (row : U8) (payload : Slice U8) (out : PE)
    (call : PreparedModel.scalar NBA_Installed.actual.sampling D before row payload false=ok (out,after)) :
    Canonical (toClaimE out) := by
  rw [sampling] at call
  exact scalar_candidate_samplers_false_canonical base D before after row payload out call

#print axioms sampling
#print axioms gamma
#print axioms ordinary
end AspisR1.NBA_Scalars
end
