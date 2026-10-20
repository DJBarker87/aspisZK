import DecoderQueryAccounting
import BinDecoderInitialStarts

set_option autoImplicit false
noncomputable section
namespace AspisR1.BinHonestStartFrames
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open CanonicalAddressEmbedding RecordedBinaryExperimentBin
abbrev p := SelectedTranscriptParams.params
abbrev L := SelectedTranscriptParams.L

theorem reject_other (a : Addr L) (hc : CanonicalByteAddress.Canonical a)
    (hn : parseAbsorb a = none) (hlen : a.toBytes.length < 75)
    (T : Table Bytes State) : dec a.toBytes T = none := by
  have hi : RawPublicInitParser.parse a = none := by
    cases hp : RawPublicInitParser.parse a with
    | none => rfl
    | some x =>
      obtain ⟨pub, root⟩ := x
      have hs := (RawPublicInitParser.parse_sound a pub root hp).2
      have hb := (PublicInitParse.parse_sound pub.pubBytes a root hs).2
      have hl := congrArg List.length hb
      simp only [List.length_append, List.length_cons, List.length_nil, bytes_length] at hl
      norm_num [PublicInitFrame.domain, PublicInitFrame.lengthBytes] at hl
      omega
  have hs : RawFullPublicSelection.select a.toBytes T = none := by
    change RawPublicSelectionLift.select L (FullPublicSelection.select p)
      (toBytes (⟨a, hc⟩ : AddrC L)) T = none
    rw [RawPublicSelectionLift.of_canonical]
    simp only [FullPublicSelection.select, hn, EarlyPublicSelection.initial, hi, Option.map_none]
  simp only [RecordedBinaryExperimentBin.dec, RawAdaptiveLiteralDecoder.decode, hs, Option.bind_none]

theorem reject_squeeze (s : State) (T : Table Bytes State) :
    dec (squeezeA p s).toBytes T = none := by
  apply reject_other _ (CanonicalByteAddress.canonical_ofBytes _ _)
  · simp [parseAbsorb, squeezeA, Addr.toBytes_ofBytes, squeeze, bytes_length]
  · simp [squeezeA, Addr.toBytes_ofBytes, squeeze, bytes_length]

theorem reject_advance (s : State) (T : Table Bytes State) :
    dec (advanceA p s).toBytes T = none := by
  apply reject_other _ (CanonicalByteAddress.canonical_ofBytes _ _)
  · simp [parseAbsorb, advanceA, Addr.toBytes_ofBytes, advance, bytes_length]
  · simp [advanceA, Addr.toBytes_ofBytes, advance, bytes_length]

/-- The extra row-zero absorb is not another initialization frame. -/
theorem reject_row_zero (s : State) (T : Table Bytes State) :
    dec (PublicInitFrame.row0 p (by norm_num [p, SelectedTranscriptParams.params,
      SelectedTranscriptParams.D]) s).toBytes T = none := by
  let a := PublicInitFrame.row0 p (by norm_num [p, SelectedTranscriptParams.params,
    SelectedTranscriptParams.D]) s
  have hc : CanonicalByteAddress.Canonical a := by
    unfold a PublicInitFrame.row0
    exact CanonicalByteAddress.canonical_ofBytes _ _
  unfold RecordedBinaryExperimentBin.dec RawAdaptiveLiteralDecoder.decode
  cases hs : RawFullPublicSelection.select a.toBytes T with
  | none => rfl
  | some pub =>
    simp only [Option.bind_some]
    unfold RawLiteralDecoderDensity.decode
    have hu : UnifiedDecoder.decode p
        (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D])
        pub a (RawBoundedTrace.table L T) = none := by
      change UnifiedDecoder.decode p _ pub
        (absorbA p s (p.lbl 0) PublicInitFrame.emptyRecord _) _ = none
      rw [UnifiedDecoder.decode_of_absorb p _ pub _ s 0 _ _ (by decide)]
      · rw [UnifiedDecoder.component_initial]
        simp [DecoderStateList.lift, UnifiedInitialDecoder.decode, InitialDecoder.decode,
          PublicInitAbsorbSeparation.parse_init_absorb_none]
      · rfl
    have hr := RawUnifiedDecoder.atCanonical_none p
      (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D])
      pub (⟨a,hc⟩ : AddrC L) T hu
    have he := RawUnifiedDecoder.decode_of_canonical p
      (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D])
      pub (⟨a,hc⟩ : AddrC L) T
    change (RawUnifiedDecoder.decode p _ pub (toBytes (⟨a,hc⟩ : AddrC L)) T).map _ = none
    rw [he, hr]
    rfl

#print axioms reject_other
#print axioms reject_squeeze
#print axioms reject_advance
#print axioms reject_row_zero
end AspisR1.BinHonestStartFrames
end
