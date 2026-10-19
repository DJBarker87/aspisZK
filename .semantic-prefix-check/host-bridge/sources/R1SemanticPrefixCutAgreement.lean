import R1SemanticPrefixCompletedAgreement
import R1TypedPrefixExtension

/-! Transport the fixed-map semantic-prefix agreement through an already-read
trace cut. The challenge-completion table and fallback remain fixed. This is
not a claim about challenges from a different table or actual oracle run. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SemanticPrefixCutAgreement

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.SourceDuplexStep
open AspisR1.SemanticPrefixCodec

abbrev State := SelectedSemanticPrefix.State
abbrev Message := SelectedSemanticPrefix.Message

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
  exact SemanticPrefixCompletedAgreement.completed_read_of_decode recoverC2 T acc row rs entries hdecode

#print axioms typed_read_append_eq
#print axioms typed_read_append_of_decode

end AspisR1.SemanticPrefixCutAgreement
end
