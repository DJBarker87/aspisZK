import R1LiteralTranscript
import R1SelectedOpeningStages

/-! Staged strict payload reads over literal-word transcript messages. These
readers inspect only the message constructor schedule and payload bytes; they
do not inspect words, challenges, or acceptance. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralOpeningStages
attribute [local instance] Classical.propDecidable

open AspisR1.InitialWalk
open AspisR1.LiteralTranscript
open AspisR1.SelectedOpeningStages
open AspisR1.CircleRecordCodec
open AspisR1.OpeningRecordCodec

variable {A : Type}

/-- Read a selected row only when the literal message has the constructor
scheduled at that row; the bytes are obtained through the erased projection. -/
def readAt (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (i : Nat) (decode : Bytes → Option A) : Option A :=
  rs[i]?.bind fun mc =>
    if LiteralTranscript.valid i mc.1 then
      match LiteralTranscript.erase mc.1 with
      | TranscriptView.Message.initial _ => none
      | TranscriptView.Message.payload bytes => decode bytes.val
    else none

theorem readAt_append_stable
    (rs tail : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (i : Nat) (decode : Bytes → Option A) (h : i < rs.length) :
    readAt (rs ++ tail) i decode = readAt rs i decode := by
  simp only [readAt, List.getElem?_append_left h]

abbrev Gamma := SelectedOpeningStages.Gamma
abbrev Kappa := SelectedOpeningStages.Kappa
abbrev First := SelectedOpeningStages.First
abbrev Second := SelectedOpeningStages.Second

def readGamma
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) :
    Option Gamma := do
  let row25 ← readAt rs 25 (CircleRecordCodec.decode 0)
  let row26 ← readAt rs 26 (CircleRecordCodec.decode 1)
  let row27 ← readAt rs 27 (OpeningRecordCodec.decode .gamma)
  pure ⟨row25, row26, row27⟩

def readKappa
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) :
    Option Kappa := do
  let gamma ← readGamma rs
  let row28 ← readAt rs 28 (OpeningRecordCodec.decode .kappa)
  pure ⟨gamma, row28⟩

def readFirst
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) :
    Option First := do
  let kappa ← readKappa rs
  let row29 ← readAt rs 29 (OpeningRecordCodec.decode .first)
  pure ⟨kappa, row29⟩

def readSecond
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) :
    Option Second := do
  let first ← readFirst rs
  let row30 ← readAt rs 30 (OpeningRecordCodec.decode .second)
  pure ⟨first, row30⟩

theorem readGamma_append_stable
    (rs tail : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (h : 27 < rs.length) : readGamma (rs ++ tail) = readGamma rs := by
  unfold readGamma
  rw [readAt_append_stable rs tail 25 _ (by omega),
      readAt_append_stable rs tail 26 _ (by omega),
      readAt_append_stable rs tail 27 _ h]

theorem readKappa_append_stable
    (rs tail : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (h : 28 < rs.length) : readKappa (rs ++ tail) = readKappa rs := by
  unfold readKappa
  rw [readGamma_append_stable rs tail (by omega),
      readAt_append_stable rs tail 28 _ h]

theorem readFirst_append_stable
    (rs tail : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (h : 29 < rs.length) : readFirst (rs ++ tail) = readFirst rs := by
  unfold readFirst
  rw [readKappa_append_stable rs tail (by omega),
      readAt_append_stable rs tail 29 _ h]

theorem readSecond_append_stable
    (rs tail : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (h : 30 < rs.length) : readSecond (rs ++ tail) = readSecond rs := by
  unfold readSecond
  rw [readFirst_append_stable rs tail (by omega),
      readAt_append_stable rs tail 30 _ h]

#print axioms readAt_append_stable
#print axioms readGamma_append_stable
#print axioms readKappa_append_stable
#print axioms readFirst_append_stable
#print axioms readSecond_append_stable

end AspisR1.LiteralOpeningStages
end
