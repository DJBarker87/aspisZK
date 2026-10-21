import S2KaniCircleRecords
import WireTx1PrefixRecords
import R4Transport2CirclePrefix

/-! Parser-to-literal circle messages composed with the existing source-state
transport. Frozen whole-verifier reachability remains a separate boundary. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.S2KaniReachedCirclePrefix
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisR1 AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open TranscriptStep SourceDigestAddresses r1_wire
open WireTx1 R4Transport2CirclePrefix

/-- The selected accessor record is from the actual parsed trace. -/
theorem accessor_circle_message (bytes : Slice U8) (pre : Prefix) (hp : Parsed bytes pre)
    (i : Fin 2) (row : U8) (hrow : row.val = 25 + i.val) (record : ValidatedRecord)
    (ha : Prefix.validated_record pre row = ok (.Ok record)) :
    record.row = row ∧ ∃ value : CircleRecordCodec.Payload i,
      CircleRecordCodec.encode value = rawBytes record.framed := by
  obtain ⟨hr,hs⟩ := accessor_bytes pre row record ha
  have hb : row.val < 27 := by have hi := i.isLt; omega
  have hrows : AspisR1.ExtractedPrefixTrace.rowOrder[row.val]? = some row := by
    have h := congrArg (fun xs : List Nat => xs[row.val]?)
      AspisR1.ExtractedPrefixTypedFull.rowOrder_values
    rw [List.getElem?_map, List.getElem?_range hb] at h
    cases he : AspisR1.ExtractedPrefixTrace.rowOrder[row.val]? with
    | none => simp [he] at h
    | some value =>
      simp only [he, Option.map_some, Option.some.injEq] at h
      have hv : value = row := UScalar.eq_of_val_eq h
      simpa only [hv] using he
  have hm : (row,record.framed) ∈
      AspisR1.ExtractedPrefixTrace.rowOrder.zip (oldPrefix pre).records.val := by
    apply List.mem_of_getElem?
    exact List.getElem?_zip_eq_some.mpr ⟨hrows,hs⟩
  obtain ⟨value,_,he⟩ := S2KaniCircleRecords.reached_circle_record bytes (oldPrefix pre) hp i row hrow record.framed hm
  refine ⟨hr,value,?_⟩
  exact he

/-- Row25 now uses the literal message constructed from parsed typed values;
no frame/codec equality hypothesis remains at this local boundary. -/
theorem parsed_circle25_state {Hash : Type} (D : aspis_core.Digest32 Hash)
    (bytes : Slice U8) (pre : Prefix) (hp : Parsed bytes pre)
    (record : ValidatedRecord)
    (ha : Prefix.validated_record pre 25#u8 = ok (.Ok record))
    (before after : SemanticTranscript Hash) (block : Bytes32)
    (hcall : SemanticTranscript.sample_block_validated D before record.row record.framed = ok (.Ok block,after))
    (P : LiteralTranscript.Prefix)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState before.state)
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out → decodeState out = H (flatten parts)) :
    ∃ value : CircleRecordCodec.Payload 0,
      CircleRecordCodec.encode value = rawBytes record.framed ∧
      UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix (extendModel H 25 P (.payload (CircleRecordCodec.message value)))) =
        decodeState after.state := by
  obtain ⟨hr,value,he⟩ := accessor_circle_message bytes pre hp 0 25#u8 rfl record ha
  have fits : (rawBytes record.framed).length ≤ SelectedTranscriptParams.D := by
    rw [← he]; simpa [SelectedTranscriptParams.D] using CircleRecordCodec.encode_length_le value
  have hm : semanticMessage record.framed fits = .payload (CircleRecordCodec.message value) := by
    unfold semanticMessage
    apply congrArg LiteralTranscript.Message.payload
    apply Subtype.ext
    exact he.symm
  have hc := circle25_state D before after record.framed block (by simpa only [hr] using hcall)
    fits P hstate H hdigest
  exact ⟨value,he,by simpa only [hm] using hc⟩

/-- Row26 consumes that parsed literal frame before the actual S2 reseed. -/
theorem parsed_circle26_reseed_state {Hash : Type} (D : aspis_core.Digest32 Hash)
    (bytes : Slice U8) (pre : Prefix) (hp : Parsed bytes pre)
    (record : ValidatedRecord)
    (ha : Prefix.validated_record pre 26#u8 = ok (.Ok record))
    (before after : SemanticTranscript Hash) (block : Bytes32)
    (hcall : SemanticTranscript.sample_block_validated D before record.row record.framed = ok (.Ok block,after))
    (hash : Hash) (opening : transcript.Transcript Hash)
    (hnew : transcript.Transcript.new D hash after.state .S2 = ok opening)
    (P : LiteralTranscript.Prefix) (htag : P.statement.tag = 2)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState before.state)
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out → decodeState out = H (flatten parts)) :
    ∃ value : CircleRecordCodec.Payload 1,
      CircleRecordCodec.encode value = rawBytes record.framed ∧
      UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix (extendModel H 26 P (.payload (CircleRecordCodec.message value)))) =
        decodeState opening.state := by
  obtain ⟨hr,value,he⟩ := accessor_circle_message bytes pre hp 1 26#u8 rfl record ha
  have fits : (rawBytes record.framed).length ≤ SelectedTranscriptParams.D := by
    rw [← he]; simpa [SelectedTranscriptParams.D] using CircleRecordCodec.encode_length_le value
  have hm : semanticMessage record.framed fits = .payload (CircleRecordCodec.message value) := by
    unfold semanticMessage
    apply congrArg LiteralTranscript.Message.payload
    apply Subtype.ext
    exact he.symm
  have hc := circle26_reseed_state D before after record.framed block (by simpa only [hr] using hcall)
    hash opening hnew fits P htag hstate H hdigest
  exact ⟨value,he,by simpa only [hm] using hc⟩

#print axioms accessor_circle_message
#print axioms parsed_circle25_state
#print axioms parsed_circle26_reseed_state
end AspisR1PublicPreparation.S2KaniReachedCirclePrefix
end
