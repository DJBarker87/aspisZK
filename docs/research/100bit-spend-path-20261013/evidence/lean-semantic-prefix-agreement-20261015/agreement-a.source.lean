import R1SemanticPrefixCodec
import R1SelectedCompletedSemantic
import R1TypedPrefixExtension

/-! Agreement of the existing strict semantic codecs on completed records.
The position supplies the row; no extra row tag is introduced. Challenges and
the C2 callback are preserved, not recovered or justified here. The append
result concerns the existing typed table cut with a fixed completion table.
This module makes no Rust-source, acceptance or oracle-provenance claim. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SemanticPrefixAgreement

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.SourceDuplexStep
open AspisR1.SemanticPrefixCodec

abbrev E := SelectedSemanticPrefix.E
abbrev State := SelectedSemanticPrefix.State
abbrev Message := SelectedSemanticPrefix.Message

/-- The live reader is exactly typed decoding followed by the fixed payload
map and the original challenges. Empty and out-of-range cases are included. -/
theorem read_eq
    (recoverC2 : State → SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (row : Nat) (xs : List (Message × E)) :
    SelectedSemanticPrefix.read recoverC2 row xs =
      (decodeFrom row (xs.map (fun q => q.1.val))).map (fun entries =>
        (entries.map (fun e => SemanticPayloadView.toMessage recoverC2 e.2.value.val)).zip
          (xs.map Prod.snd)) := by
  induction xs generalizing row with
  | nil => rfl
  | cons item rest ih =>
      rcases item with ⟨message, challenge⟩
      by_cases hrow : row < 25
      · cases hdecode : SemanticRecordCodec.decode ⟨row, hrow⟩ message.val with
        | none =>
            simp [SelectedSemanticPrefix.read, decodeFrom, TypedPrefixParser.decode,
              decodeOne, hrow, hdecode]
        | some payload =>
            have hrest := ih (row + 1)
            unfold decodeFrom at hrest
            cases htail : TypedPrefixParser.decode decodeOne (row + 1)
                (rest.map (fun q => q.1.val)) <;>
              simp [SelectedSemanticPrefix.read, decodeFrom, TypedPrefixParser.decode,
                decodeOne, hrow, hdecode, hrest, htail]
      · simp [SelectedSemanticPrefix.read, decodeFrom, TypedPrefixParser.decode,
          decodeOne, hrow]

/-- Successful typed decoding discharges the live reader's success premise. -/
theorem read_of_decode
    (recoverC2 : State → SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (row : Nat) (xs : List (Message × E)) (entries : List Entry)
    (hdecode : decodeFrom row (xs.map (fun q => q.1.val)) = some entries) :
    SelectedSemanticPrefix.read recoverC2 row xs =
      some ((entries.map (fun e => SemanticPayloadView.toMessage recoverC2 e.2.value.val)).zip
        (xs.map Prod.snd)) := by
  rw [read_eq, hdecode]
  rfl

/-- In particular, the zip never silently drops a decoded payload. -/
theorem decoded_length (row : Nat) (xs : List (Message × E)) (entries : List Entry)
    (hdecode : decodeFrom row (xs.map (fun q => q.1.val)) = some entries) :
    entries.length = (xs.map Prod.snd).length := by
  simpa only [List.length_map] using
    TypedPrefixParser.decode_length decodeOne row (xs.map (fun q => q.1.val)) entries hdecode

/-- Completion changes no message bytes, regardless of how challenges are
supplied by the table and fallback function. -/
theorem completed_records
    (T : Table (Addr SelectedTranscriptParams.L) State)
    (acc : Addr SelectedTranscriptParams.L → State) (row : Nat)
    (rs : List (Rec Message)) :
    (SelectedCompletedSemantic.pairs T acc row rs).map (fun q => q.1.val) =
      rs.map (fun r => r.2.2.1.val) := by
  induction rs generalizing row with
  | nil => rfl
  | cons r rest ih =>
      simpa only [SelectedCompletedSemantic.pairs, completeRounds, List.map_cons] using
        congrArg (List.cons r.2.2.1.val) (ih (row + 1))

theorem completed_read_eq
    (recoverC2 : State → SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (T : Table (Addr SelectedTranscriptParams.L) State)
    (acc : Addr SelectedTranscriptParams.L → State) (row : Nat)
    (rs : List (Rec Message)) :
    SelectedSemanticPrefix.read recoverC2 row (SelectedCompletedSemantic.pairs T acc row rs) =
      (decodeFrom row (rs.map (fun r => r.2.2.1.val))).map (fun entries =>
        (entries.map (fun e => SemanticPayloadView.toMessage recoverC2 e.2.value.val)).zip
          ((SelectedCompletedSemantic.pairs T acc row rs).map Prod.snd)) := by
  rw [read_eq, completed_records]

theorem completed_read_of_decode
    (recoverC2 : State → SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (T : Table (Addr SelectedTranscriptParams.L) State)
    (acc : Addr SelectedTranscriptParams.L → State) (row : Nat)
    (rs : List (Rec Message)) (entries : List Entry)
    (hdecode : decodeFrom row (rs.map (fun r => r.2.2.1.val)) = some entries) :
    SelectedSemanticPrefix.read recoverC2 row (SelectedCompletedSemantic.pairs T acc row rs) =
      some ((entries.map (fun e => SemanticPayloadView.toMessage recoverC2 e.2.value.val)).zip
        ((SelectedCompletedSemantic.pairs T acc row rs).map Prod.snd)) := by
  rw [completed_read_eq, hdecode]
  rfl

/-- Consume the existing completed-record theorem with its read-success
premise supplied by the codec, retaining the exact completed challenges. -/
theorem completed_semChalsZ_of_decode
    (recoverC2 : State → SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (T : Table (Addr SelectedTranscriptParams.L) State)
    (acc : Addr SelectedTranscriptParams.L → State) (row : Nat)
    (rs : List (Rec Message)) (entries : List Entry)
    (hdecode : decodeFrom row (rs.map (fun r => r.2.2.1.val)) = some entries) :
    R0P.Mask.semChalsZ (SelectedSemanticPrefixFacts.lift
      ((entries.map (fun e => SemanticPayloadView.toMessage recoverC2 e.2.value.val)).zip
        ((SelectedCompletedSemantic.pairs T acc row rs).map Prod.snd))) =
      some ((SelectedCompletedSemantic.pairs T acc row rs).map Prod.snd) := by
  exact SelectedCompletedSemantic.semChalsZ_read recoverC2 row T acc rs _
    (completed_read_of_decode recoverC2 T acc row rs entries hdecode)

/-- Appending the trace preserves the recovered typed records at an address
already read. The separate challenge-completion table remains fixed. -/
theorem typed_read_append_eq
    (recoverC2 : State → SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (pubBytes : Bytes) (t T : Table (Addr SelectedTranscriptParams.L) State)
    (tr tail : List (Addr SelectedTranscriptParams.L × State))
    (a : Addr SelectedTranscriptParams.L) (ha : a ∈ tr.map Prod.fst)
    (fuel : Nat) (endpoint : State)
    (acc : Addr SelectedTranscriptParams.L → State) (row : Nat) :
    (UnifiedSemanticRecovery.typed SelectedTranscriptParams.params pubBytes
      (tableBefore t (tr ++ tail) a) fuel endpoint).bind (fun recovered =>
        SelectedSemanticPrefix.read recoverC2 row
          (SelectedCompletedSemantic.pairs T acc row recovered.2)) =
    (UnifiedSemanticRecovery.typed SelectedTranscriptParams.params pubBytes
      (tableBefore t tr a) fuel endpoint).bind (fun recovered =>
        SelectedSemanticPrefix.read recoverC2 row
          (SelectedCompletedSemantic.pairs T acc row recovered.2)) := by
  rw [TypedPrefixExtension.semantic_typed_append_eq
    SelectedTranscriptParams.params pubBytes t tr tail a ha fuel endpoint]

theorem typed_read_append_of_decode
    (recoverC2 : State → SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (pubBytes : Bytes) (t T : Table (Addr SelectedTranscriptParams.L) State)
    (tr tail : List (Addr SelectedTranscriptParams.L × State))
    (a : Addr SelectedTranscriptParams.L) (ha : a ∈ tr.map Prod.fst)
    (fuel : Nat) (endpoint c1 : State)
    (acc : Addr SelectedTranscriptParams.L → State) (row : Nat)
    (rs : List (Rec Message)) (entries : List Entry)
    (htyped : UnifiedSemanticRecovery.typed SelectedTranscriptParams.params pubBytes
      (tableBefore t tr a) fuel endpoint = some (c1, rs))
    (hdecode : decodeFrom row (rs.map (fun r => r.2.2.1.val)) = some entries) :
    (UnifiedSemanticRecovery.typed SelectedTranscriptParams.params pubBytes
      (tableBefore t (tr ++ tail) a) fuel endpoint).bind (fun recovered =>
        SelectedSemanticPrefix.read recoverC2 row
          (SelectedCompletedSemantic.pairs T acc row recovered.2)) =
      some ((entries.map (fun e => SemanticPayloadView.toMessage recoverC2 e.2.value.val)).zip
        ((SelectedCompletedSemantic.pairs T acc row rs).map Prod.snd)) := by
  rw [typed_read_append_eq recoverC2 pubBytes t T tr tail a ha fuel endpoint acc row, htyped]
  exact completed_read_of_decode recoverC2 T acc row rs entries hdecode

#print axioms read_eq
#print axioms read_of_decode
#print axioms decoded_length
#print axioms completed_records
#print axioms completed_read_eq
#print axioms completed_read_of_decode
#print axioms completed_semChalsZ_of_decode
#print axioms typed_read_append_eq
#print axioms typed_read_append_of_decode

end AspisR1.SemanticPrefixAgreement
end
