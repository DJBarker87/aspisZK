import CanonicalCutEnrichedTranscript

/-! Install the scheduled word-bearing constructors without changing erased
messages or sampler programs. This does not bind the chosen words to source
commitments; wordsFromRawCuts is the existing intended instantiation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawLiteralWordScheduleDecoration
open FS FS2
open AspisV8R19.SourceDuplexStep
open LiteralTranscript CanonicalCutEnrichedTranscript

/-- The constructor schedule is determined by the row; payload bytes survive. -/
def payloadAt (w : Words) (i : Nat) (b : LiteralTranscript.BytesMessage) :
    LiteralTranscript.Message :=
  if i = 2 then .c2 b w.c2 else if i = 30 then .second b w.final else .payload b

def message (w : Words) (i : Nat) : LiteralTranscript.Message → LiteralTranscript.Message
  | .initial root _ => .initial root w.c1
  | .payload b => payloadAt w i b
  | .c2 b _ => payloadAt w i b
  | .second b _ => payloadAt w i b

def decoratePrefix (w : Words) (P : LiteralTranscript.Prefix) : LiteralTranscript.Prefix :=
  ⟨P.statement,P.rounds.mapIdx fun i mc => (message w i mc.1,mc.2)⟩

@[simp] theorem erase_payloadAt (w : Words) (i : Nat) (b : LiteralTranscript.BytesMessage) :
    LiteralTranscript.erase (payloadAt w i b) = .payload b := by
  by_cases h2 : i = 2
  · simp only [payloadAt,if_pos h2,LiteralTranscript.erase]
  · by_cases h30 : i = 30
    · simp only [payloadAt,if_neg h2,if_pos h30,LiteralTranscript.erase]
    · simp only [payloadAt,if_neg h2,if_neg h30,LiteralTranscript.erase]

@[simp] theorem erase_message (w : Words) (i : Nat) (m : LiteralTranscript.Message) :
    LiteralTranscript.erase (message w i m) = LiteralTranscript.erase m := by
  cases m with
  | initial root word => rfl
  | payload b => exact erase_payloadAt w i b
  | c2 b word => exact erase_payloadAt w i b
  | second b word => exact erase_payloadAt w i b

theorem payloadAt_valid (w : Words) (i : Nat) (b : LiteralTranscript.BytesMessage)
    (hi0 : i ≠ 0) (hi33 : i < 33) : LiteralTranscript.valid i (payloadAt w i b) := by
  unfold payloadAt
  split
  · rename_i h; subst i; trivial
  · rename_i h2
    split
    · rename_i h; subst i; trivial
    · rename_i h30
      simp only [LiteralTranscript.valid]
      exact ⟨hi0,h2,h30,hi33⟩

private theorem erase_rounds (w : Words)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) (start : Nat) :
    (rs.mapIdx (fun i mc => (message w (start+i) mc.1,mc.2))).map
        (fun mc => (LiteralTranscript.erase mc.1,mc.2)) =
      rs.map (fun mc => (LiteralTranscript.erase mc.1,mc.2)) := by
  induction rs generalizing start with
  | nil => rfl
  | cons mc rs ih =>
    simp only [List.mapIdx_cons,List.map_cons,erase_message]
    congr 1
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (start+1)

theorem erase_prefix (w : Words) (P : LiteralTranscript.Prefix) :
    LiteralTranscript.erasePrefix (decoratePrefix w P) = LiteralTranscript.erasePrefix P := by
  cases P with
  | mk statement rounds =>
    unfold decoratePrefix LiteralTranscript.erasePrefix
    congr 1
    simpa only [Nat.zero_add] using erase_rounds w rounds 0

theorem sampler_eq (w : Words) (i : Nat)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    LiteralTranscript.samp i (decoratePrefix w P) (message w i m) = LiteralTranscript.samp i P m := by
  simp only [LiteralTranscript.samp,erase_prefix,erase_message]

theorem prefix_ext (w : Words) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (c : LiteralTranscript.Challenge) :
    decoratePrefix w (P.ext m c) = (decoratePrefix w P).ext (message w P.round m) c := by
  cases P
  simp [decoratePrefix,FS.Prefix.ext,FS.Prefix.round,List.mapIdx_append]

#print axioms erase_message
#print axioms payloadAt_valid
#print axioms erase_prefix
#print axioms sampler_eq
#print axioms prefix_ext
end AspisR1.RawLiteralWordScheduleDecoration
end
