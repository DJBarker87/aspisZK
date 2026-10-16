import CanonicalCutEnrichedTranscript
import R1LiteralClassifier

/-! Restore literal commitment metadata to the erased decoder output. Words
may be chosen from the fixed decoded prefix/current message; they do not depend
on the current challenge. The existing literal row density is reused exactly. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralDecoderEnrichment
open FS FS2
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open LiteralTranscript CanonicalCutEnrichedTranscript
abbrev ErasedMessage := TranscriptView.Message LiteralTranscript.BytesMessage
abbrev ErasedPrefix := UnifiedSampler.Prefix LiteralTranscript.BytesMessage
  AspisWideTower.WideExact SelectedTranscriptParams.L

def message (w : Words) (i : Nat) : ErasedMessage → LiteralTranscript.Message
  | .initial r => .initial r w.c1
  | .payload b => if i = 2 then .c2 b w.c2 else if i = 30 then .second b w.final else .payload b

def rounds (w : Words) : Nat → List (ErasedMessage × LiteralTranscript.Challenge) →
    List (LiteralTranscript.Message × LiteralTranscript.Challenge)
  | _, [] => []
  | i, mc :: rest => (message w i mc.1,mc.2) :: rounds w (i+1) rest

def restorePrefix (w : Words) (P : ErasedPrefix) : LiteralTranscript.Prefix :=
  ⟨P.statement,rounds w 0 P.rounds⟩

@[simp] theorem erase_message (w : Words) (i : Nat) (m : ErasedMessage) :
    LiteralTranscript.erase (message w i m) = m := by
  cases m with
  | initial r => rfl
  | payload b =>
      by_cases h2 : i = 2
      · simp [message, h2, LiteralTranscript.erase]
      · by_cases h30 : i = 30
        · simp [message, h2, h30, LiteralTranscript.erase]
        · simp [message, h2, h30, LiteralTranscript.erase]

@[simp] theorem rounds_length (w : Words) (i : Nat)
    (rs : List (ErasedMessage × LiteralTranscript.Challenge)) :
    (rounds w i rs).length = rs.length := by
  induction rs generalizing i with
  | nil => rfl
  | cons q rest ih => simp only [rounds,List.length_cons,ih]

theorem erase_rounds (w : Words) (i : Nat)
    (rs : List (ErasedMessage × LiteralTranscript.Challenge)) :
    (rounds w i rs).map (fun mc => (LiteralTranscript.erase mc.1,mc.2)) = rs := by
  induction rs generalizing i with
  | nil => rfl
  | cons q rest ih => simp only [rounds,List.map_cons,erase_message,ih]

@[simp] theorem erase_prefix (w : Words) (P : ErasedPrefix) :
    LiteralTranscript.erasePrefix (restorePrefix w P) = P := by
  cases P with
  | mk pub rs => simp [restorePrefix,LiteralTranscript.erasePrefix,erase_rounds]

@[simp] theorem prefix_round (w : Words) (P : ErasedPrefix) : (restorePrefix w P).round = P.round := by
  simp [restorePrefix,FS.Prefix.round]

theorem message_of_valid (w : Words) (i : Nat) (m : LiteralTranscript.Message)
    (h : LiteralTranscript.valid i m) :
    message w i (LiteralTranscript.erase m) = enrichMessage w m := by
  cases m with
  | initial r v => rfl
  | payload b =>
      have h2 : i ≠ 2 := by
        intro hi
        subst i
        simp [LiteralTranscript.valid] at h
      have h30 : i ≠ 30 := by
        intro hi
        subst i
        simp [LiteralTranscript.valid] at h
      simp [message,LiteralTranscript.erase,enrichMessage,h2,h30]
  | c2 b v =>
      have hi : i = 2 := by
        unfold LiteralTranscript.valid at h
        split at h <;> simp_all
      simp [message,LiteralTranscript.erase,enrichMessage,hi]
  | second b v =>
      have hi : i = 30 := by
        unfold LiteralTranscript.valid at h
        split at h <;> simp_all
      simp [message,LiteralTranscript.erase,enrichMessage,hi]

theorem density (w : Words) (P : ErasedPrefix) (m : ErasedMessage) (hi : P.round < 33) :
    independentMean (UnifiedSampler.samp SelectedTranscriptParams.params
      (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
      P.round P m).toProgram
      (fun v => indicator (LiteralClassifier.bad (restorePrefix w P) (message w P.round m) v.2)) ≤
      LiteralClassifier.budget P.round := by
  have h := LiteralClassifier.density (restorePrefix w P) (message w P.round m) (by simpa using hi)
  simpa only [prefix_round,LiteralTranscript.samp,erase_prefix,erase_message] using h

#print axioms erase_prefix
#print axioms message_of_valid
#print axioms density
end AspisR1.LiteralDecoderEnrichment
end
