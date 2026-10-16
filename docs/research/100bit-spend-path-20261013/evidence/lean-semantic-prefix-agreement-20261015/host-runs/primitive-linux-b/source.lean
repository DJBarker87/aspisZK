import R1SemanticPrefixCodec
import R1SelectedSemanticPrefix

/-! Agreement of the existing strict semantic codecs on completed records.
The position supplies the row; no extra row tag is introduced. Challenges and
the C2 callback are preserved, not recovered or justified here. This module makes no Rust-source, acceptance or oracle-provenance claim. -/
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

#print axioms read_eq
#print axioms read_of_decode
#print axioms decoded_length

end AspisR1.SemanticPrefixAgreement
end
