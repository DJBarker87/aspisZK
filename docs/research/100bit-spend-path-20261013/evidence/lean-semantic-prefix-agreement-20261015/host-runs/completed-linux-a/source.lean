import R1SemanticPrefixAgreement
import R1SelectedCompletedSemantic

/-! Lift the fixed-map semantic agreement to the existing completed-record
sampler. The table, fallback challenge function and C2 callback are unchanged;
this module does not prove their runtime or oracle provenance. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SemanticPrefixCompletedAgreement

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.SourceDuplexStep
open AspisR1.SemanticPrefixCodec

abbrev E := SemanticPrefixAgreement.E
abbrev State := SemanticPrefixAgreement.State
abbrev Message := SemanticPrefixAgreement.Message

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
  rw [SemanticPrefixAgreement.read_eq, completed_records]

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

#print axioms completed_records
#print axioms completed_read_eq
#print axioms completed_read_of_decode
#print axioms completed_semChalsZ_of_decode

end AspisR1.SemanticPrefixCompletedAgreement
end
