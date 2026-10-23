import S1OriginalSerializerInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1CurrentCaller.OriginalSerializerInstallation
open AspisR1PublicPreparation AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1Post25SamplerOrdinaryRankV1 AspisR1CurrentPreparedClaim.Concrete
def ExactSerializedRankTrace {H M Cv : Type} {L : Nat}
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H) (out : AspisR1PublicPreparation.verifier.Prepared)
    (scratch : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize) : Prop :=
  ∃ (start t1 t2 t3 : transcript.Transcript H)
    (alpha0 : AspisR1PublicPreparation.aspis_core.field.WideExact)
    (gammaBlock kappaBlock alphaBlock : Array U8 32#usize),
    transcript.Transcript.new D hash sem.transcript.state v.variant=ok start ∧
    transcript.Transcript.block D start 27#u8 v.y1=ok (gammaBlock,t1) ∧
    AspisR1ClaimPreparedBridge.GammaRankMeaning gammaBlock out.gamma ∧
    transcript.Transcript.block D t1 28#u8 (Array.to_slice (expectedBytes v.inactive))=ok (kappaBlock,t2) ∧
    OrdinaryRankMeaning kappaBlock out.kappa ∧
    transcript.Transcript.block D t2 29#u8 v.round0=ok (alphaBlock,t3) ∧
    OrdinaryRankMeaning alphaBlock alpha0 ∧
    RankedTailFacts AspisS1M31Embedding.Total.embed D p pubInput root length v out alpha0 t3

/-- Same complete challenge trace with row28's payload fixed to the exact
unchanged source serializer bytes. The free serialization-operation premise
and independently chosen byte witness are removed by the total source law. -/
theorem jointRankTrace_exact_bytes {H M Cv : Type} {L : Nat}
    (sampling : PreparedModel.Boundaries) (D : aspis_core.Digest32 H)
    (p : FS2.Duplex.Params M Cv L) (pubInput : Slice U8)
    (root : TranscriptStep.Bytes32) (length : U32) (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H) (out : AspisR1PublicPreparation.verifier.Prepared)
    (scratch : Array aspis_core.field.WideExact 29#usize) :
    JointRankTrace (withOriginalSerializer sampling) AspisS1M31Embedding.Total.embed
      D p pubInput root length sem v hash out scratch ↔
    ExactSerializedRankTrace D p pubInput root length sem v hash out scratch := by
  constructor
  · rintro ⟨start,t1,t2,t3,bytes,a,gb,kb,ab,hn,hb,hg,hrg,hk,hrk,ha,hra,ht⟩
    change sourceBytes v.inactive=ok bytes at hb
    rw [sourceBytes_total] at hb
    have he : expectedBytes v.inactive=bytes := Result.ok.inj hb
    subst bytes
    exact ⟨start,t1,t2,t3,a,gb,kb,ab,hn,hg,hrg,hk,hrk,ha,hra,ht⟩
  · rintro ⟨start,t1,t2,t3,a,gb,kb,ab,hn,hg,hrg,hk,hrk,ha,hra,ht⟩
    exact ⟨start,t1,t2,t3,expectedBytes v.inactive,a,gb,kb,ab,hn,
      sourceBytes_total v.inactive,hg,hrg,hk,hrk,ha,hra,ht⟩

#print axioms jointRankTrace_exact_bytes
end AspisR1CurrentCaller.OriginalSerializerInstallation
