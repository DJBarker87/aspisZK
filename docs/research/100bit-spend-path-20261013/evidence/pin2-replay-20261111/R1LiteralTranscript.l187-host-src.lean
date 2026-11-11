import R1UnifiedSampler
import R1LiteralTypedWords
import R1SelectedTranscriptParams

/-! Literal-word message carrier and projection to the selected sampler.
The words are part of messages before the corresponding challenges. This
is syntax and transcript projection only: no accepted-proof recovery,
classifier density, Merkle compiler, or source refinement is asserted. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralTranscript

open FS FS2
open AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev E := AspisWideTower.WideExact
abbrev BytesMessage := SelectedTranscriptParams.Message
abbrev C1Word := LiteralTypedWords.C1Word
abbrev C2Word := LiteralTypedWords.C2Word
abbrev VWord := AspisPool.AlgorithmicCircleDecoderV7.FinalWord E
abbrev Public := UnifiedSampler.Public SelectedTranscriptParams.L
abbrev Challenge := TranscriptView.Challenge E

/-- Only the three commitment-bearing rows carry literal words. The original
commitment bytes remain in the projection; correspondence is a later compiler
obligation, not a condition baked into the types. -/
inductive Message
  | initial (root : State) (word : C1Word)
  | payload (bytes : BytesMessage)
  | c2 (bytes : BytesMessage) (word : C2Word)
  | second (bytes : BytesMessage) (word : VWord)

def erase : Message → TranscriptView.Message BytesMessage
  | .initial root _ => .initial root
  | .payload bytes => .payload bytes
  | .c2 bytes _ => .payload bytes
  | .second bytes _ => .payload bytes

abbrev Prefix := FS.Prefix Public Message Challenge

def erasePrefix (P : Prefix) : UnifiedSampler.Prefix BytesMessage E SelectedTranscriptParams.L :=
  ⟨P.statement, P.rounds.map fun mc => (erase mc.1, mc.2)⟩

/-- Constructor schedule only. Strict row payload parsing is a separate check. -/
def valid : Nat → Message → Prop
  | 0, .initial _ _ => True
  | 2, .c2 _ _ => True
  | 30, .second _ _ => True
  | i, .payload _ => i ≠ 0 ∧ i ≠ 2 ∧ i ≠ 30 ∧ i < 33
  | _, _ => False

def c1At (rs : List (Message × Challenge)) : Option C1Word :=
  rs[0]?.bind fun mc => match mc.1 with
    | .initial _ word => some word
    | _ => none

def c2At (rs : List (Message × Challenge)) : Option C2Word :=
  rs[2]?.bind fun mc => match mc.1 with
    | .c2 _ word => some word
    | _ => none

def vAt (rs : List (Message × Challenge)) : Option VWord :=
  rs[30]?.bind fun mc => match mc.1 with
    | .second _ word => some word
    | _ => none

def samp (i : Nat) (P : Prefix) (m : Message) :
    Sampler (FS2.Duplex.Addr SelectedTranscriptParams.L) State Challenge :=
  UnifiedSampler.samp SelectedTranscriptParams.params
    (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
    i (erasePrefix P) (erase m)

theorem erasePrefix_round (P : Prefix) : (erasePrefix P).round = P.round := by
  simp [erasePrefix, FS.Prefix.round]

theorem erasePrefix_ext (P : Prefix) (m : Message) (c : Challenge) :
    erasePrefix (P.ext m c) = (erasePrefix P).ext (erase m) c := by
  simp [erasePrefix, FS.Prefix.ext]

theorem c1At_append (rs tail : List (Message × Challenge)) (h : 0 < rs.length) :
    c1At (rs ++ tail) = c1At rs := by
  simp only [c1At, List.getElem?_append_left h]

theorem c2At_append (rs tail : List (Message × Challenge)) (h : 2 < rs.length) :
    c2At (rs ++ tail) = c2At rs := by
  simp only [c2At, List.getElem?_append_left h]

theorem vAt_append (rs tail : List (Message × Challenge)) (h : 30 < rs.length) :
    vAt (rs ++ tail) = vAt rs := by
  simp only [vAt, List.getElem?_append_left h]

#print axioms erasePrefix_round
#print axioms erasePrefix_ext
#print axioms c1At_append
#print axioms c2At_append
#print axioms vAt_append

end AspisR1.LiteralTranscript
end
