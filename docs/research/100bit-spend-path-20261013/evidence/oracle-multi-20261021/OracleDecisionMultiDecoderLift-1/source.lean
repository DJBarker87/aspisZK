import BinHonestStartFrames

/-! A symbolic decoder lift. Keeping the canonical address and current table
abstract avoids normalizing a concrete 131072-cell padded address. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionMultiDecoderLift
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open CanonicalAddressEmbedding
abbrev p := SelectedTranscriptParams.params
abbrev L := SelectedTranscriptParams.L

theorem recognizes (pub : LiteralTranscript.Public) (a : AddrC L) (T : Table Bytes State)
    (hp : RawFullPublicSelection.select (toBytes a) T = some pub)
    (hu : UnifiedDecoder.decode p (by norm_num [p, SelectedTranscriptParams.params,
      SelectedTranscriptParams.D]) pub a.val (RawBoundedTrace.table L T) ≠ none) :
    RecordedBinaryExperimentBin.dec (toBytes a) T ≠ none := by
  unfold RecordedBinaryExperimentBin.dec
  rw [RawAdaptiveLiteralDecoder.decode_of_public _ _ _ _ _ hp]
  unfold RawLiteralDecoderDensity.decode
  rw [RawUnifiedDecoder.decode_of_canonical p _ pub a T]
  cases he : UnifiedDecoder.decode p _ pub a.val (RawBoundedTrace.table L T) with
  | none => exact False.elim (hu he)
  | some result =>
      rcases result with ⟨s, ps, g⟩
      rw [RawUnifiedDecoder.atCanonical_of_decode p
        (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]) pub a T s ps g he]
      simp only [Option.map_some, ne_eq, reduceCtorEq, not_false_eq_true]

#print axioms recognizes
end AspisR1.OracleDecisionMultiDecoderLift
end
