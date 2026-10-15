import R1LiteralTranscript

/-! A recursive literal-message run and its selected byte-message projection.
This is transcript plumbing only; it supplies no decoder, acceptance, or
source-correspondence result. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralRun

open FS FS2
open AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev E := AspisWideTower.WideExact
abbrev L := SelectedTranscriptParams.L
abbrev Address := FS2.Duplex.Addr L
abbrev State := AspisV8R19.SourceDuplexStep.State
abbrev Public := LiteralTranscript.Public
abbrev Message := LiteralTranscript.Message
abbrev Challenge := LiteralTranscript.Challenge
abbrev Prefix := LiteralTranscript.Prefix
abbrev BytesMessage := LiteralTranscript.BytesMessage

/-- Run the literal-word message carrier using the sampler supplied by that
carrier. -/
def transcript (H : Address → State) (pub : Public) (messages : Nat → Message) :
    Nat → Prefix
  | 0 => FS.emptyPrefix pub
  | n + 1 =>
      let P := transcript H pub messages n
      P.ext (messages n)
        (eval H (LiteralTranscript.samp n P (messages n)).toProgram).2

/-- Run the erased byte-message schedule directly through the selected
unified sampler. -/
def erasedTranscript (H : Address → State) (pub : Public) (messages : Nat → Message) :
    Nat → UnifiedSampler.Prefix BytesMessage E L
  | 0 => FS.emptyPrefix pub
  | n + 1 =>
      let P := erasedTranscript H pub messages n
      P.ext (LiteralTranscript.erase (messages n))
        (eval H (UnifiedSampler.samp SelectedTranscriptParams.params
          (by norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D])
          n P (LiteralTranscript.erase (messages n))).toProgram).2

/-- Erasing each literal message commutes with the recursive transcript run. -/
theorem erase_transcript (H : Address → State) (pub : Public)
    (messages : Nat → Message) (n : Nat) :
    LiteralTranscript.erasePrefix (transcript H pub messages n) =
      erasedTranscript H pub messages n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [transcript, erasedTranscript, LiteralTranscript.erasePrefix_ext,
        LiteralTranscript.samp, ih]

/-- The recursive literal transcript contains exactly one round per step. -/
theorem transcript_round (H : Address → State) (pub : Public)
    (messages : Nat → Message) (n : Nat) :
    (transcript H pub messages n).round = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (transcript H pub messages n).rounds.length = n at ih
      simpa [transcript, FS.Prefix.round, FS.Prefix.ext] using congrArg Nat.succ ih

/-- The three indexed literal-word reads are unaffected by appending a suffix
once all their positions are already present. -/
theorem reads_append_stable (rs tail : List (Message × Challenge))
    (h : 30 < rs.length) :
    LiteralTranscript.c1At (rs ++ tail) = LiteralTranscript.c1At rs ∧
    LiteralTranscript.c2At (rs ++ tail) = LiteralTranscript.c2At rs ∧
    LiteralTranscript.vAt (rs ++ tail) = LiteralTranscript.vAt rs := by
  exact ⟨LiteralTranscript.c1At_append rs tail (by omega),
    LiteralTranscript.c2At_append rs tail (by omega),
    LiteralTranscript.vAt_append rs tail h⟩

#print axioms erase_transcript
#print axioms transcript_round
#print axioms reads_append_stable

end AspisR1.LiteralRun
end
