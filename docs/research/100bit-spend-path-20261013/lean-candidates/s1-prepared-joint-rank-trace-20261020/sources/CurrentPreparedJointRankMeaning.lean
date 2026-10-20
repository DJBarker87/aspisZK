import CurrentPreparedJointRankTrace
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1PublicPreparation
open AspisR1Post25SamplerOrdinaryRankV1
def JointRankTrace {H M Cv : Type} {L : Nat} (sampling : PreparedModel.Boundaries)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (sem : r1_semantic.Verified H)
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
    RankedTailFacts embed D p pubInput root length v out alpha0 t3

theorem prepared_installed_joint_rank_trace {H M Cv : Type} {L : Nat}
    (sampling : PreparedModel.Boundaries)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (out : verifier.Prepared)
    (scratch scratchIn : Array aspis_core.field.WideExact 29#usize)
    (h : PreparedScratchModel.prepare
      (AspisR1ClaimPreparedBridge.concreteBoundaries (installedBoundaries sampling embed))
      D sem v hash scratchIn=ok (.Ok out,scratch)) :
    JointRankTrace sampling embed D p pubInput root length sem v hash out scratch := by
  obtain ⟨start,t1,t2,t3,bytes,alpha0,gb,kb,ab,hseed,hb,hgb,hrg,hkb,hrk,hab,hra,ht⟩ :=
    prepared_installed_joint_rank_prefix sampling embed D sem v hash out scratch scratchIn h
  exact ⟨start,t1,t2,t3,bytes,alpha0,gb,kb,ab,hseed,hb,hgb,hrg,hkb,hrk,hab,hra,
    tail_ranked_facts sampling embed D p pubInput root length sem v out.gamma out.kappa
      alpha0 t3 out scratch ht⟩

#print axioms prepared_installed_joint_rank_trace
end AspisR1ClaimPreparedBridge.InstalledMeaning
