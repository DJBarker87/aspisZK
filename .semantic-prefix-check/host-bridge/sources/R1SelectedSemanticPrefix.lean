import R1SemanticPayloadView
import R1SelectedTranscriptParams

/-! Strict semantic decoding of a selected typed-message prefix.  The C2
root recovery callback remains explicit; this module adds no acceptance or
trace assumptions. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedSemanticPrefix

open R0P R0P.Mask R0P.SemSource
open AspisR1.SemanticRecordCodec AspisR1.SemanticPayloadView
open AspisR1.SelectedTranscriptParams

abbrev E := SemanticPayloadView.E
abbrev State := SemanticPayloadView.State
abbrev Message := SelectedTranscriptParams.Message

def read (recoverC2 : State → AspisR1.SemanticPayloadView.InitialWord ×
      AspisR1.SemanticPayloadView.InitialWord) :
    Nat → List (Message × E) → Option (List (SemMsgZ E × E))
  | _, [] => some []
  | offset, (message, challenge) :: rest =>
      if h : offset < 25 then
        match SemanticRecordCodec.decode ⟨offset, h⟩ message.val with
        | none => none
        | some payload =>
            (read recoverC2 (offset + 1) rest).map
              (fun out => (SemanticPayloadView.toMessage recoverC2 payload.val,
                challenge) :: out)
      else none

theorem read_length (recoverC2 : State →
    AspisR1.SemanticPayloadView.InitialWord × AspisR1.SemanticPayloadView.InitialWord)
    (offset : Nat) (xs : List (Message × E)) (out : List (SemMsgZ E × E))
    (h : read recoverC2 offset xs = some out) : out.length = xs.length := by
  induction xs generalizing offset out with
  | nil => simp [read] at h; subst out; rfl
  | cons item rest ih =>
      rcases item with ⟨message, challenge⟩
      by_cases hoff : offset < 25
      · cases hdecode : SemanticRecordCodec.decode ⟨offset, hoff⟩ message.val with
        | none => simp [read, hoff, hdecode] at h
        | some payload =>
          cases htail : read recoverC2 (offset + 1) rest with
          | none => simp [read, hoff, hdecode, htail] at h
          | some tail =>
            have hout :
                (SemanticPayloadView.toMessage recoverC2 payload.val, challenge) :: tail = out := by
              simpa [read, hoff, hdecode, htail] using h
            cases hout
            have hlen := ih (offset + 1) tail htail
            simp [hlen]
      · simp [read, hoff] at h

theorem read_append (recoverC2 : State →
    AspisR1.SemanticPayloadView.InitialWord × AspisR1.SemanticPayloadView.InitialWord)
    (offset : Nat) (xs ys : List (Message × E)) :
    read recoverC2 offset (xs ++ ys) =
      (read recoverC2 offset xs).bind fun left =>
        (read recoverC2 (offset + xs.length) ys).map fun right => left ++ right := by
  induction xs generalizing offset with
  | nil => simp [read]
  | cons item rest ih =>
      rcases item with ⟨message, challenge⟩
      by_cases hoff : offset < 25
      · cases hdecode : SemanticRecordCodec.decode ⟨offset, hoff⟩ message.val with
        | none => simp [read, hoff, hdecode]
        | some payload =>
          rw [List.cons_append]
          simp only [read, dif_pos hoff, hdecode]
          rw [ih (offset + 1)]
          have hindex : offset + ((message, challenge) :: rest).length =
              (offset + 1) + rest.length := by
            simp only [List.length_cons]
            omega
          rw [hindex]
          cases hl : read recoverC2 (offset + 1) rest <;>
            cases hr : read recoverC2 ((offset + 1) + rest.length) ys <;>
            simp [hl, hr]
      · simp [read, hoff]

#print axioms read_length
#print axioms read_append

end AspisR1.SelectedSemanticPrefix
end
