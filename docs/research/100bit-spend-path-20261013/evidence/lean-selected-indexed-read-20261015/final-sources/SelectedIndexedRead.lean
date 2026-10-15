import R1IndexedMessage
import R1SelectedSemanticMessages
import R1CircleRecordCodec
import R1OpeningRecordCodec

/-! Indexed read wrappers for the selected row codecs. They connect an
encoded bounded message to the already typed parser at its selected label;
they do not interpret recovered words or establish source/acceptance facts. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedIndexedRead

open AspisR1.SelectedTranscriptParams

abbrev Byte := AspisR1.SemanticCoefficientCodec.Byte
abbrev Bytes := List Byte

def readTyped {A : Type} (i : Nat) (label : Byte) (data : Bytes)
    (d : Bytes → Option A) : Option A :=
  (AspisR1.IndexedMessage.read AspisR1.SelectedTranscriptParams.params i label data).bind
    (fun m => d m.val)

theorem readTyped_encoded {A : Type} (i : Nat)
    (m : AspisR1.SelectedTranscriptParams.Message) (d : Bytes → Option A)
    (a : A) (h : d m.val = some a) :
    readTyped i (AspisR1.SelectedTranscriptParams.params.lbl i) m.val d = some a := by
  unfold readTyped
  have hread : AspisR1.IndexedMessage.read AspisR1.SelectedTranscriptParams.params i
      (AspisR1.SelectedTranscriptParams.params.lbl i) m.val = some m := by
    simpa [AspisR1.SelectedTranscriptParams.params,
      AspisR1.SelectedTranscriptParams.enc] using
      (AspisR1.IndexedMessage.read_encoded AspisR1.SelectedTranscriptParams.params i m)
  simp [hread, h]

theorem readTyped_sound {A : Type} (i : Nat) (label : Byte) (data : Bytes)
    (d : Bytes → Option A) (a : A)
    (h : readTyped i label data d = some a) :
    label = AspisR1.SelectedTranscriptParams.params.lbl i ∧ d data = some a := by
  unfold readTyped at h
  rcases Option.bind_eq_some_iff.mp h with ⟨m, hread, hd⟩
  have hs := AspisR1.IndexedMessage.read_sound
    AspisR1.SelectedTranscriptParams.params i label data m hread
  rcases hs with ⟨hlabel, _hdec, henc⟩
  have hmdata : m.val = data := by
    simpa [AspisR1.SelectedTranscriptParams.params,
      AspisR1.SelectedTranscriptParams.enc] using henc
  exact ⟨hlabel, by rw [hmdata] at hd; exact hd⟩

theorem semantic_read_encoded {row : Fin 25}
    (payload : AspisR1.SemanticRecordCodec.RowPayload row) :
    readTyped row.val (AspisR1.SelectedTranscriptParams.params.lbl row.val)
      (AspisR1.SelectedSemanticMessages.ofTyped payload).val
      (AspisR1.SemanticRecordCodec.decode row) = some payload := by
  apply readTyped_encoded
  simpa [AspisR1.SelectedSemanticMessages.ofTyped] using
    (AspisR1.SemanticRecordCodec.decode_encode payload)

theorem circle_read_encoded (row : Fin 2)
    (payload : AspisR1.CircleRecordCodec.Payload row) :
    readTyped (25 + row.val)
      (AspisR1.SelectedTranscriptParams.params.lbl (25 + row.val))
      (AspisR1.CircleRecordCodec.message payload).val
      (AspisR1.CircleRecordCodec.decode row) = some payload := by
  apply readTyped_encoded
  exact AspisR1.CircleRecordCodec.decode_encode payload

def openingRowIndex : AspisR1.OpeningRecordCodec.Row → Nat
  | .gamma => 0
  | .kappa => 1
  | .first => 2
  | .second => 3
  | .final => 4
  | .rho => 5

theorem opening_read_encoded {row : AspisR1.OpeningRecordCodec.Row}
    (payload : AspisR1.OpeningRecordCodec.Payload row) :
    readTyped (27 + openingRowIndex row)
      (AspisR1.SelectedTranscriptParams.params.lbl (27 + openingRowIndex row))
      (AspisR1.OpeningRecordCodec.message payload).val
      (AspisR1.OpeningRecordCodec.decode row) = some payload := by
  apply readTyped_encoded
  exact AspisR1.OpeningRecordCodec.decode_encode payload

theorem label_injective {i j : Nat} (hi : i < 33) (hj : j < 33)
    (h : AspisR1.SelectedTranscriptParams.params.lbl i =
      AspisR1.SelectedTranscriptParams.params.lbl j) : i = j := by
  have hv := congrArg Fin.val h
  change (AspisR1.SelectedTranscriptParams.label i).val =
    (AspisR1.SelectedTranscriptParams.label j).val at hv
  rw [AspisR1.SelectedTranscriptParams.label_val i hi,
    AspisR1.SelectedTranscriptParams.label_val j hj] at hv
  omega

#print axioms readTyped_encoded
#print axioms readTyped_sound
#print axioms semantic_read_encoded
#print axioms circle_read_encoded
#print axioms opening_read_encoded
#print axioms label_injective

end AspisR1.SelectedIndexedRead
end
