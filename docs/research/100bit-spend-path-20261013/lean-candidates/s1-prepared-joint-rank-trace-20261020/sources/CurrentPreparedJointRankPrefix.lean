import CurrentPreparedInstalledMeaning
import CurrentPreparedOrdinaryRankV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete
open AspisR1PublicPreparation
open PreparedFromQmSourceBridge
open AspisR1Post25SamplerOrdinaryRankV1
local notation "ordinaryBoundary" => AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary

def JointRankPrefix {H : Type} (sampling : PreparedModel.Boundaries)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H) (out : verifier.Prepared)
    (scratch : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize) : Prop :=
  ∃ (start t1 t2 t3 : transcript.Transcript H) (bytes : Array U8 32#usize)
    (alpha0 : AspisR1PublicPreparation.aspis_core.field.WideExact)
    (gammaBlock kappaBlock alphaBlock : Array U8 32#usize),
    transcript.Transcript.new D hash sem.transcript.state v.variant=ok start ∧
    (installedBoundaries sampling embed).toBytes v.inactive=ok bytes ∧
    transcript.Transcript.block D start 27#u8 v.y1=ok (gammaBlock,t1) ∧
    GammaRankMeaning gammaBlock out.gamma ∧
    transcript.Transcript.block D t1 28#u8 (Array.to_slice bytes)=ok (kappaBlock,t2) ∧
    OrdinaryRankMeaning kappaBlock out.kappa ∧
    transcript.Transcript.block D t2 29#u8 v.round0=ok (alphaBlock,t3) ∧
    OrdinaryRankMeaning alphaBlock alpha0 ∧
    PreparedScratchReachability.Tail
      (AspisR1ClaimPreparedBridge.concreteBoundaries (installedBoundaries sampling embed))
      D sem v out.gamma out.kappa alpha0 t3 out scratch

theorem prepared_installed_joint_rank_prefix {H : Type}
    (sampling : PreparedModel.Boundaries)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H) (out : verifier.Prepared)
    (scratch scratchIn : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize)
    (h : PreparedScratchModel.prepare
      (AspisR1ClaimPreparedBridge.concreteBoundaries (installedBoundaries sampling embed))
      D sem v hash scratchIn=ok (.Ok out,scratch)) :
    JointRankPrefix sampling embed D sem v hash out scratch := by
  obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,hseed,hg,hb,hk,ha,ht⟩ :=
    PreparedScratchReachability.prepare_success
      (AspisR1ClaimPreparedBridge.concreteBoundaries (installedBoundaries sampling embed))
      D sem v hash out scratch scratchIn h
  let base := withSourceFromQm (CurrentQueryRho.withConcreteQueries sampling embed)
  have hfields := tail_concrete_run (installedBoundaries sampling embed)
    D sem v gamma kappa alpha0 t3 out scratch ht
  change PreparedModel.scalar (withCandidateGamma (ordinaryBoundary base))
    D start 27#u8 v.y1 true=ok (gamma,t1) at hg
  change PreparedModel.scalar (ordinaryBoundary (withCandidateGamma base))
    D t1 28#u8 (Array.to_slice bytes) false=ok (kappa,t2) at hk
  change PreparedModel.scalar (ordinaryBoundary (withCandidateGamma base))
    D t2 29#u8 v.round0 false=ok (alpha0,t3) at ha
  obtain ⟨gb,hgb,hrg⟩ := scalar_candidate_gamma_rank (ordinaryBoundary base)
    D start t1 27#u8 v.y1 gamma hg
  obtain ⟨kb,hkb,hrk⟩ := scalar_candidate_ordinary_rank (withCandidateGamma base)
    D t1 t2 28#u8 (Array.to_slice bytes) kappa hk
  obtain ⟨ab,hab,hra⟩ := scalar_candidate_ordinary_rank (withCandidateGamma base)
    D t2 t3 29#u8 v.round0 alpha0 ha
  refine ⟨start,t1,t2,t3,bytes,alpha0,gb,kb,ab,hseed,hb,hgb,?_,hkb,?_,hab,hra,?_⟩
  · simpa only [hfields.1] using hrg
  · simpa only [hfields.2.1] using hrk
  · simpa only [hfields.1,hfields.2.1] using ht

#print axioms prepared_installed_joint_rank_prefix
end AspisR1ClaimPreparedBridge.InstalledMeaning
