import PreparedP6InactiveRow28V1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1PreparedP6InactiveRow28TraceV2

open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete
open AspisR1PreparedP6InactiveRow28V1
open AspisR1PreparedSourcePowersJointRankV1

/-- One witness package retains the complete joint rank trace and enriches its
same row-28 byte array with strict parser success and all eight coordinate
roundtrip equalities. The source bounds are derived from successful View
selection by the imported row-28 proof. -/
theorem prepared_entry_row28_with_joint_trace
    {H M Cv : Type} {L : Nat}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (p : FS2.Duplex.Params M Cv L) (pubInput : Slice U8)
    (root : Array U8 32#usize) (length : U32)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (proof semantic y1 : Slice U8)
    (v : AspisR1SelectedWideViewV1.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (scratch scratchIn : Array PE 29#usize)
    (hview : AspisR1SelectedWideViewV1.verifier.candidate.wide_view
      proof semantic y1=ok (.Ok v))
    (hprepare : AspisR1PublicPreparation.PreparedScratchModel.entry
      (sourceBoundaries (installedBoundaries (withP6InactiveSerializer sampling) embed))
      D sem (preparedView v) hash scratchIn=ok (.Ok out,scratch)) :
  ∃ (start t1 t2 t3 : AspisR1PublicPreparation.transcript.Transcript H)
      (bytes : Array U8 32#usize)
      (alpha0 : AspisR1PublicPreparation.aspis_core.field.WideExact)
      (gammaBlock kappaBlock alphaBlock : Array U8 32#usize)
      (parsed : AspisR1CandidateParser.field.wide_exact.WideExact),
      AspisR1PublicPreparation.transcript.Transcript.new D hash sem.transcript.state
        (preparedView v).variant=ok start ∧
      AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes
        (preparedToSource (prepCarrier v.inactive))=ok bytes ∧
      AspisR1PublicPreparation.transcript.Transcript.block D start 27#u8 v.y1
        =ok (gammaBlock,t1) ∧
      AspisR1ClaimPreparedBridge.GammaRankMeaning gammaBlock out.gamma ∧
      AspisR1PublicPreparation.transcript.Transcript.block D t1 28#u8
        (Array.to_slice bytes)=ok (kappaBlock,t2) ∧
      AspisR1Post25SamplerOrdinaryRankV1.OrdinaryRankMeaning kappaBlock out.kappa ∧
      AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
        (Array.to_slice bytes)=ok (some parsed) ∧
      parsed.c0.c0.a.val=v.inactive.c0.c0.a.val ∧ parsed.c0.c0.b.val=v.inactive.c0.c0.b.val ∧
      parsed.c0.c1.a.val=v.inactive.c0.c1.a.val ∧ parsed.c0.c1.b.val=v.inactive.c0.c1.b.val ∧
      parsed.c1.c0.a.val=v.inactive.c1.c0.a.val ∧ parsed.c1.c0.b.val=v.inactive.c1.c0.b.val ∧
      parsed.c1.c1.a.val=v.inactive.c1.c1.a.val ∧ parsed.c1.c1.b.val=v.inactive.c1.c1.b.val ∧
      AspisR1PublicPreparation.transcript.Transcript.block D t2 29#u8 v.round0
        =ok (alphaBlock,t3) ∧
      AspisR1Post25SamplerOrdinaryRankV1.OrdinaryRankMeaning alphaBlock alpha0 ∧
      AspisR1ClaimPreparedBridge.InstalledMeaning.RankedTailFacts embed D p pubInput
        root length v out alpha0 t3 := by
  have hcanonical : Canonical (toClaimE (prepCarrier v.inactive)) :=
    AspisR1SelectedWideViewV1.wide_view_inactive_canonical proof semantic y1 v hview
  have hprep : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (sourceBoundaries (installedBoundaries (withP6InactiveSerializer sampling) embed))
      D sem (preparedView v) hash scratchIn=ok (.Ok out,scratch) := by
    simpa only [AspisR1PublicPreparation.PreparedScratchModel.entry] using hprepare
  have htrace := AspisR1PreparedSourcePowersJointRankV1.prepared_sourcePowers_joint_rank_trace
      (withP6InactiveSerializer sampling) embed D p pubInput root length sem
      (preparedView v) hash out scratch scratchIn hprep
  obtain ⟨start,t1,t2,t3,bytes,alpha0,gb,kb,ab,
    hseed,hbytes,hgb,hgrank,hkb,hkrank,hab,harank,htail⟩ := htrace
  change (withP6InactiveSerializer sampling).toBytes (prepCarrier v.inactive)=ok bytes at hbytes
  rw [withP6InactiveSerializer_toBytes] at hbytes
  obtain ⟨serialized,hserializer,_,parsed,hparse,h0,h1,h2,h3,h4,h5,h6,h7⟩ :=
    prepared_inactive_serializer_roundtrip (prepCarrier v.inactive) hcanonical
  have heq : serialized=bytes := Result.ok.inj (hserializer.symm.trans hbytes)
  subst serialized
  exact ⟨start,t1,t2,t3,bytes,alpha0,gb,kb,ab,parsed,
    hseed,hserializer,hgb,hgrank,hkb,hkrank,hparse,
    by simpa [prepCarrier] using h0, by simpa [prepCarrier] using h1,
    by simpa [prepCarrier] using h2, by simpa [prepCarrier] using h3,
    by simpa [prepCarrier] using h4, by simpa [prepCarrier] using h5,
    by simpa [prepCarrier] using h6, by simpa [prepCarrier] using h7,
    hab,harank,htail⟩

#print axioms prepared_entry_row28_with_joint_trace
end AspisR1PreparedP6InactiveRow28TraceV2
