import R1LiteralTranscript
import R1SemanticPayloadView

/-! A strict selected semantic-prefix reader for literal-word transcript
messages. The literal C2 word supplies the callback when a decoded semantic
record is a C2 root; no future callback is part of the reader. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralSemanticPrefix
attribute [local instance] Classical.propDecidable

open R0P.Mask R0P.SemSource
open AspisR1.SemanticRecordCodec
open AspisR1.SemanticPayloadView
open AspisR1.LiteralTranscript
open AspisR1.TranscriptView

abbrev E := AspisWideTower.WideExact
abbrev State := SemanticPayloadView.State
abbrev InitialWord := SemanticPayloadView.InitialWord
abbrev C2Word := LiteralTranscript.C2Word
abbrev Message := LiteralTranscript.Message
abbrev Challenge := LiteralTranscript.Challenge

/-- The two QM31 lanes of a literal C2 word as the semantic view's pair of
initial words. -/
def c2Pair (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E)
    (word : C2Word) : InitialWord × InitialWord :=
  (fun i => eK (word i 0), fun i => eK (word i 1))

/-- Parse a literal transcript message at a selected semantic row. -/
def parseMessage (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E)
    (row : Fin 25) (m : Message) : Option (SemMsgZ E) :=
  if LiteralTranscript.valid row.val m then
    match m with
    | .initial _ _ => some (.base .none)
    | .payload bytes =>
        (SemanticRecordCodec.decode row bytes.val).map fun payload =>
          SemanticPayloadView.toMessage (fun _ => (fun _ => 0, fun _ => 0)) payload.val
    | .c2 bytes word =>
        (SemanticRecordCodec.decode row bytes.val).map fun payload =>
          SemanticPayloadView.toMessage (fun _ => c2Pair eK word) payload.val
    | .second _ _ => none
  else none

/-- Strict semantic parser over literal messages and ordinary challenges. -/
def read (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E) :
    Nat → List (Message × Challenge) → Option (List (SemMsgZ E × E))
  | _, [] => some []
  | offset, (message, challenge) :: rest =>
      if h : offset < 25 then
        match challenge.1 with
        | .ordinary c =>
            (parseMessage eK ⟨offset, h⟩ message).bind fun parsed =>
              (read eK (offset + 1) rest).map fun out => (parsed, c) :: out
        | .queries _ => none
      else none

theorem read_length (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E)
    (offset : Nat) (xs : List (Message × Challenge)) (out : List (SemMsgZ E × E))
    (h : read eK offset xs = some out) : out.length = xs.length := by
  induction xs generalizing offset out with
  | nil => simp [read] at h; subst out; rfl
  | cons item rest ih =>
      rcases item with ⟨message, challenge⟩
      by_cases hoff : offset < 25
      · cases hvalue : challenge.1 with
        | queries result => simp [read, hoff, hvalue] at h
        | ordinary c =>
            cases hmessage : parseMessage eK ⟨offset, hoff⟩ message with
            | none => simp [read, hoff, hvalue, hmessage] at h
            | some parsed =>
                cases htail : read eK (offset + 1) rest with
                | none => simp [read, hoff, hvalue, hmessage, htail] at h
                | some tail =>
                    have hout : (parsed, c) :: tail = out := by
                      simpa [read, hoff, hvalue, hmessage, htail] using h
                    cases hout
                    have hlen := ih (offset + 1) tail htail
                    simp [hlen]
      · simp [read, hoff] at h

theorem read_append (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E)
    (offset : Nat) (xs ys : List (Message × Challenge)) :
    read eK offset (xs ++ ys) =
      (read eK offset xs).bind fun left =>
        (read eK (offset + xs.length) ys).map fun right => left ++ right := by
  induction xs generalizing offset with
  | nil => simp [read]
  | cons item rest ih =>
      rcases item with ⟨message, challenge⟩
      by_cases hoff : offset < 25
      · cases hvalue : challenge.1 with
        | queries result => simp [read, hoff, hvalue]
        | ordinary c =>
            cases hmessage : parseMessage eK ⟨offset, hoff⟩ message with
            | none => simp [read, hoff, hvalue, hmessage]
            | some parsed =>
                rw [List.cons_append]
                simp only [read, dif_pos hoff, hvalue, hmessage]
                rw [ih (offset + 1)]
                have hindex : offset + ((message, challenge) :: rest).length =
                    (offset + 1) + rest.length := by
                  simp only [List.length_cons]
                  omega
                rw [hindex]
                cases hl : read eK (offset + 1) rest <;>
                  cases hr : read eK ((offset + 1) + rest.length) ys <;>
                  simp [hl, hr]
      · simp [read, hoff]

#print axioms read_length
#print axioms read_append

end AspisR1.LiteralSemanticPrefix
end
