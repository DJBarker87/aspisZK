import S5P6SourceStrictEncodingV1
import ToBytesP6OutputInvariantV1
import SelectedWideViewPreparedEntryV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1PreparedP6InactiveRow28V1

open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete
open AspisR1.RetainedFieldByteCodec
open AspisR1SelectedWideViewV1
open AspisR1PreparedSourcePowersBoundariesV1
open AspisR1PreparedSourcePowersJointRankV1

abbrev SourceWide := _root_.P6ToBytes.IndexedCarrierBridge.SourceWide

def preparedToSource (x : PE) : SourceWide :=
  { c0 := { c0 := {a:=x.c0.c0.a,b:=x.c0.c0.b}, c1:={a:=x.c0.c1.a,b:=x.c0.c1.b} },
    c1 := { c0 := {a:=x.c1.c0.a,b:=x.c1.c0.b}, c1:={a:=x.c1.c1.a,b:=x.c1.c1.b} } }

def withP6InactiveSerializer (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries) :
    AspisR1PublicPreparation.PreparedModel.Boundaries :=
  { sampling with toBytes := fun x =>
      AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes (preparedToSource x) }

theorem withP6InactiveSerializer_toBytes
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries) (x : PE) :
    (withP6InactiveSerializer sampling).toBytes x =
      AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes (preparedToSource x) := rfl

theorem prepared_canonical_source_limb_bounds (x : PE)
    (hc : Canonical (toClaimE x)) :
    ∀ i : Fin 8,
      (AspisR1S5P6SourceStrictEncodingV1.wordAt (preparedToSource x) i).val <
        AspisR1.RetainedFieldByteCodec.m31Modulus := by
  have hfull : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1CurrentPreparedClaim.Concrete.toFull (toClaimE x)) := by
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1CurrentPreparedClaim.Concrete.toFull (toClaimE x))
    exact hc
  simp only [AspisR1CurrentWide.Proof.CanonicalWide,
    AspisR1CurrentWide.Proof.CanonicalQM,
    AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
    AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
    AspisR1CurrentPreparedClaim.Concrete.toFull,
    AspisR1CurrentPreparedClaim.Concrete.toQM,
    AspisR1CurrentPreparedClaim.Concrete.toCM,
    AspisR1ClaimPreparedBridge.toClaimE,
    AspisR1ClaimPreparedBridge.toClaimQ] at hfull
  rcases hfull with ⟨⟨⟨h0,h1⟩,⟨h2,h3⟩⟩,⟨⟨h4,h5⟩,⟨h6,h7⟩⟩⟩
  have hP : AspisR1.ExtractedCurrentTowerAdd.P =
      AspisR1.RetainedFieldByteCodec.m31Modulus := by
    norm_num [AspisR1.ExtractedCurrentTowerAdd.P,
      AspisR1.ExtractedCurrentM31AddSub.P,
      AspisR1.RetainedFieldByteCodec.m31Modulus,
      AspisR1.RetainedFieldByteCodec.rawCandidateCount]
  intro i
  fin_cases i
  · change x.c0.c0.a.val < AspisR1.RetainedFieldByteCodec.m31Modulus
    change x.c0.c0.a.val < AspisR1.ExtractedCurrentTowerAdd.P at h0
    simpa only [hP] using h0
  · change x.c0.c0.b.val < AspisR1.RetainedFieldByteCodec.m31Modulus
    change x.c0.c0.b.val < AspisR1.ExtractedCurrentTowerAdd.P at h1
    simpa only [hP] using h1
  · change x.c0.c1.a.val < AspisR1.RetainedFieldByteCodec.m31Modulus
    change x.c0.c1.a.val < AspisR1.ExtractedCurrentTowerAdd.P at h2
    simpa only [hP] using h2
  · change x.c0.c1.b.val < AspisR1.RetainedFieldByteCodec.m31Modulus
    change x.c0.c1.b.val < AspisR1.ExtractedCurrentTowerAdd.P at h3
    simpa only [hP] using h3
  · change x.c1.c0.a.val < AspisR1.RetainedFieldByteCodec.m31Modulus
    change x.c1.c0.a.val < AspisR1.ExtractedCurrentTowerAdd.P at h4
    simpa only [hP] using h4
  · change x.c1.c0.b.val < AspisR1.RetainedFieldByteCodec.m31Modulus
    change x.c1.c0.b.val < AspisR1.ExtractedCurrentTowerAdd.P at h5
    simpa only [hP] using h5
  · change x.c1.c1.a.val < AspisR1.RetainedFieldByteCodec.m31Modulus
    change x.c1.c1.a.val < AspisR1.ExtractedCurrentTowerAdd.P at h6
    simpa only [hP] using h6
  · change x.c1.c1.b.val < AspisR1.RetainedFieldByteCodec.m31Modulus
    change x.c1.c1.b.val < AspisR1.ExtractedCurrentTowerAdd.P at h7
    simpa only [hP] using h7

theorem prepared_inactive_serializer_roundtrip (x : PE)
    (hc : Canonical (toClaimE x)) :
    ∃ bytes : Array U8 32#usize,
      AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes
        (preparedToSource x)=ok bytes ∧
      bytes.val=_root_.P6ToBytes.OutputInvariant.serializedWords (preparedToSource x) ∧
      ∃ parsed : AspisR1CandidateParser.field.wide_exact.WideExact,
        AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
          (Array.to_slice bytes)=ok (some parsed) ∧
        parsed.c0.c0.a.val=x.c0.c0.a.val ∧ parsed.c0.c0.b.val=x.c0.c0.b.val ∧
        parsed.c0.c1.a.val=x.c0.c1.a.val ∧ parsed.c0.c1.b.val=x.c0.c1.b.val ∧
        parsed.c1.c0.a.val=x.c1.c0.a.val ∧ parsed.c1.c0.b.val=x.c1.c0.b.val ∧
        parsed.c1.c1.a.val=x.c1.c1.a.val ∧ parsed.c1.c1.b.val=x.c1.c1.b.val := by
  have hb := prepared_canonical_source_limb_bounds x hc
  obtain ⟨bytes,hbytes,parsed,hparse,h0,h1,h2,h3,h4,h5,h6,h7⟩ :=
    AspisR1S5P6SourceStrictEncodingV1.source_serializer_parser_roundtrip_fieldwise
      (preparedToSource x) hb
  obtain ⟨bytes',hbytes',hcontents⟩ :=
    _root_.P6ToBytes.OutputInvariant.to_le_bytes_output_contents (preparedToSource x)
  have heq : bytes=bytes' := Result.ok.inj (hbytes.symm.trans hbytes')
  subst bytes'
  refine ⟨bytes,hbytes,hcontents,parsed,hparse,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [preparedToSource] using h0
  · simpa [preparedToSource] using h1
  · simpa [preparedToSource] using h2
  · simpa [preparedToSource] using h3
  · simpa [preparedToSource] using h4
  · simpa [preparedToSource] using h5
  · simpa [preparedToSource] using h6
  · simpa [preparedToSource] using h7

/-- The selected source View's inactive value is serialized by the extracted
P6 body and those same bytes feed row 28 of the successful preparation trace. -/
theorem prepared_entry_row28_uses_source_serializer
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
  ∃ (start t1 t2 : AspisR1PublicPreparation.transcript.Transcript H)
      (bytes block : Array U8 32#usize),
      AspisR1PublicPreparation.transcript.Transcript.new D hash sem.transcript.state
        (preparedView v).variant=ok start ∧
      AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes
        (preparedToSource (prepCarrier v.inactive))=ok bytes ∧
      AspisR1PublicPreparation.transcript.Transcript.block D t1 28#u8
        (Array.to_slice bytes)=ok (block,t2) ∧
      ∃ parsed : AspisR1CandidateParser.field.wide_exact.WideExact,
        AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled
          (Array.to_slice bytes)=ok (some parsed) ∧
        parsed.c0.c0.a.val=v.inactive.c0.c0.a.val ∧
        parsed.c0.c0.b.val=v.inactive.c0.c0.b.val ∧
        parsed.c0.c1.a.val=v.inactive.c0.c1.a.val ∧
        parsed.c0.c1.b.val=v.inactive.c0.c1.b.val ∧
        parsed.c1.c0.a.val=v.inactive.c1.c0.a.val ∧
        parsed.c1.c0.b.val=v.inactive.c1.c0.b.val ∧
        parsed.c1.c1.a.val=v.inactive.c1.c1.a.val ∧
        parsed.c1.c1.b.val=v.inactive.c1.c1.b.val := by
  have hcanonical : Canonical (toClaimE (prepCarrier v.inactive)) :=
    wide_view_inactive_canonical proof semantic y1 v hview
  have hprep : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (sourceBoundaries (installedBoundaries (withP6InactiveSerializer sampling) embed))
      D sem (preparedView v) hash scratchIn=ok (.Ok out,scratch) := by
    simpa only [AspisR1PublicPreparation.PreparedScratchModel.entry] using hprepare
  obtain ⟨start,t1,t2,t3,bytes,alpha0,gb,kb,ab,
    hseed,hbytes,hgb,hgrank,hkb,hkrank,hab,harank,htail⟩ :=
    AspisR1PreparedSourcePowersJointRankV1.prepared_sourcePowers_joint_rank_trace
      (withP6InactiveSerializer sampling) embed D p pubInput root length sem
      (preparedView v) hash out scratch scratchIn hprep
  change (withP6InactiveSerializer sampling).toBytes (prepCarrier v.inactive)=ok bytes at hbytes
  rw [withP6InactiveSerializer_toBytes] at hbytes
  obtain ⟨bytes',hserializer,_,parsed,hparse,h0,h1,h2,h3,h4,h5,h6,h7⟩ :=
    prepared_inactive_serializer_roundtrip (prepCarrier v.inactive) hcanonical
  have heq : bytes'=bytes := Result.ok.inj (hserializer.symm.trans hbytes)
  subst bytes'
  exact ⟨start,t1,t2,bytes,kb,hseed,hserializer,hkb,
    parsed,hparse,by simpa [prepCarrier] using h0, by simpa [prepCarrier] using h1,
    by simpa [prepCarrier] using h2, by simpa [prepCarrier] using h3,
    by simpa [prepCarrier] using h4, by simpa [prepCarrier] using h5,
    by simpa [prepCarrier] using h6, by simpa [prepCarrier] using h7⟩

#print axioms prepared_canonical_source_limb_bounds
#print axioms prepared_inactive_serializer_roundtrip
#print axioms prepared_entry_row28_uses_source_serializer

end AspisR1PreparedP6InactiveRow28V1
