import RawChecksCommitmentFormats
import RawCompiledChecksOriginalSchedule
import RawCompiledTranscriptRoundAlignmentV7

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.RawChecksInjectionFormat

open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.RawCutProverCompiler
open AspisR1.RawCutTranscriptRun
open AspisR1.RawCutWordsFromView
open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.LiteralTranscript
open AspisR1.RawChecksCommitmentFormats

abbrev Bytes := AspisV8R19.DuplexFrames.Bytes
abbrev State := AspisV8R19.SourceDuplexStep.State

/-- Exact local copy of the predicate used by
`RawAdaptiveDecoderInjection.CommitmentMessages`; kept local so this checked
format lemma can compile without importing the large adaptive owner. -/
def CommitmentMessages (pf : LiteralProtocol.Proof) : Prop :=
  ∃ (r1 : State) (w1 : LiteralTranscript.C1Word)
    (b2 : LiteralTranscript.BytesMessage) (w2 : LiteralTranscript.C2Word) (r2 : State)
    (b30 : LiteralTranscript.BytesMessage) (w30 : LiteralTranscript.VWord)
    (v30 : OpeningRecordCodec.Payload .second),
    pf 0 = .initial r1 w1 ∧ pf 2 = .c2 b2 w2 ∧ pf 30 = .second b30 w30 ∧
    SemanticRecordCodec.decode ⟨2, by decide⟩ b2.val = some ⟨.c2Root r2, by rfl⟩ ∧
    OpeningRecordCodec.decode .second b30.val = some v30

private theorem valid_enrichMessage (w : Words) (i : Nat) (m : Message) :
    LiteralTranscript.valid i (enrichMessage w m) ↔ LiteralTranscript.valid i m := by
  cases m with
  | initial root word =>
      by_cases hi : i = 0
      · subst i; simp [LiteralTranscript.valid, enrichMessage]
      · simp [LiteralTranscript.valid, enrichMessage, hi]
  | payload bytes => simp [LiteralTranscript.valid, enrichMessage]
  | c2 bytes word =>
      by_cases hi : i = 2
      · subst i; simp [LiteralTranscript.valid, enrichMessage]
      · simp [LiteralTranscript.valid, enrichMessage, hi]
  | second bytes word =>
      by_cases hi : i = 30
      · subst i; simp [LiteralTranscript.valid, enrichMessage]
      · simp [LiteralTranscript.valid, enrichMessage, hi]

/-- Successful literal Checks derive all parser/constructor parts of the
actual adaptive decoder's format interface. The public tag remains a separate
source-interface premise because the checked model stores it independently. -/
theorem checks_imply_injection_format
    (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State)
    (original annotated : RunView)
    (horiginal : original = eval H (experiment P (verifier decoder d)))
    (hannotated : annotated = eval H (experiment
      (compiled decoder d (RawCutWordsFromView.buildWords decoder) P) (verifier decoder d)))
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (hrows : rs = ((LiteralByteProtocol.protocol decoder).transcript H
      annotated.2.1.1 annotated.2.1.2 33).rounds)
    (checks : LiteralAcceptanceTerminal.Checks annotated.2.1.1 rs)
    (htag : original.2.1.1.tag = 2) :
    (∀ i < 33, LiteralTranscript.valid i (original.2.1.2 i)) ∧
    original.2.1.1.tag = 2 ∧ CommitmentMessages original.2.1.2 := by
  subst rs
  have hvalid030 := RawCompiledChecksOriginalSchedule.checks_force_original_constructor_schedule
    decoder d P H original annotated horiginal hannotated
    (by simpa only using checks)
  let w := RawCutWordsFromView.buildWords decoder original
  let extendRun : RunView → RunView := fun v =>
    (v.1 ++ (eval H (verifier decoder d v.2.1.1 v.2.1.2)).1,
      ((v.2.1.1, RawCutTranscriptRun.proof
        (RawCutWordsFromView.buildWords decoder v) v.2.1.2), v.2.2))
  have hext : eval H (experiment
      (compiled decoder d (RawCutWordsFromView.buildWords decoder) P) (verifier decoder d)) =
      extendRun (eval H (experiment P (verifier decoder d))) := by
    change eval H (experiment
      (compiled decoder d (RawCutWordsFromView.buildWords decoder) P) (verifier decoder d)) = _
    simpa only [extendRun] using
      (compiled_experiment_eval decoder d (RawCutWordsFromView.buildWords decoder) P H)
  have hextOriginal : extendRun original =
      extendRun (eval H (experiment P (verifier decoder d))) := congrArg extendRun horiginal
  have hrun : annotated =
      let v := original
      (v.1 ++ (eval H (verifier decoder d v.2.1.1 v.2.1.2)).1,
        ((v.2.1.1, RawCutTranscriptRun.proof w v.2.1.2), v.2.2)) := by
    calc
      annotated = eval H (experiment
          (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
          (verifier decoder d)) := hannotated
      _ = extendRun (eval H (experiment P (verifier decoder d))) := hext
      _ = extendRun original := hextOriginal.symm
      _ = _ := rfl
  have hproof : annotated.2.1.2 = RawCutTranscriptRun.proof w original.2.1.2 :=
    congrArg (fun v : RunView => v.2.1.2) hrun
  have hvalid31 : LiteralTranscript.valid 31 (original.2.1.2 31) := by
    have hidx := LiteralByteRunFacts.transcript_index decoder H
      annotated.2.1.1 annotated.2.1.2 33 31 (by omega)
    have hpair := Option.some.inj (checks.entry31.symm.trans hidx)
    have hvAnn : LiteralTranscript.valid 31 (annotated.2.1.2 31) := by
      have hfst : checks.m31 = annotated.2.1.2 31 := congrArg Prod.fst hpair
      exact hfst ▸ checks.valid31
    have hat := congrArg (fun pf : LiteralProtocol.Proof => pf 31) hproof
    have hvEnr : LiteralTranscript.valid 31
        (enrichMessage w (original.2.1.2 31)) := by simpa only [hat, RawCutTranscriptRun.proof] using hvAnn
    exact (valid_enrichMessage w 31 (original.2.1.2 31)).mp hvEnr
  have hvalid32 : LiteralTranscript.valid 32 (original.2.1.2 32) := by
    have hidx := LiteralByteRunFacts.transcript_index decoder H
      annotated.2.1.1 annotated.2.1.2 33 32 (by omega)
    have hpair := Option.some.inj (checks.entry32.symm.trans hidx)
    have hvAnn : LiteralTranscript.valid 32 (annotated.2.1.2 32) := by
      have hfst : checks.m32 = annotated.2.1.2 32 := congrArg Prod.fst hpair
      exact hfst ▸ checks.valid32
    have hat := congrArg (fun pf : LiteralProtocol.Proof => pf 32) hproof
    have hvEnr : LiteralTranscript.valid 32
        (enrichMessage w (original.2.1.2 32)) := by simpa only [hat, RawCutTranscriptRun.proof] using hvAnn
    exact (valid_enrichMessage w 32 (original.2.1.2 32)).mp hvEnr
  have hvalid : ∀ i < 33, LiteralTranscript.valid i (original.2.1.2 i) := by
    intro i hi
    by_cases hsmall : i ≤ 30
    · exact hvalid030 i hsmall
    · have hi31 : i = 31 ∨ i = 32 := by omega
      rcases hi31 with hi31 | hi32
      · simpa [hi31] using hvalid31
      · simpa [hi32] using hvalid32
  have hparses := checks_give_commitment_parses decoder H annotated
    ((LiteralByteProtocol.protocol decoder).transcript H
      annotated.2.1.1 annotated.2.1.2 33).rounds checks rfl
  rcases hparses with ⟨⟨r2, b2a, w2a, ha2, hdecode2a⟩,
    ⟨payload30, b30a, w30a, ha30, hdecode30a⟩⟩
  have hshape0 : ∃ root word, original.2.1.2 0 = .initial root word := by
    have hv := hvalid 0 (by omega)
    cases hm : original.2.1.2 0 with
    | initial root word => exact ⟨root, word, rfl⟩
    | payload bytes => simp [LiteralTranscript.valid, hm] at hv
    | c2 bytes word => simp [LiteralTranscript.valid, hm] at hv
    | second bytes word => simp [LiteralTranscript.valid, hm] at hv
  have hshape2 : ∃ b word, original.2.1.2 2 = .c2 b word := by
    have hv := hvalid 2 (by omega)
    cases hm : original.2.1.2 2 with
    | c2 b word => exact ⟨b, word, rfl⟩
    | initial root word => simp [LiteralTranscript.valid, hm] at hv
    | payload bytes => simp [LiteralTranscript.valid, hm] at hv
    | second bytes word => simp [LiteralTranscript.valid, hm] at hv
  have hshape30 : ∃ b word, original.2.1.2 30 = .second b word := by
    have hv := hvalid 30 (by omega)
    cases hm : original.2.1.2 30 with
    | second b word => exact ⟨b, word, rfl⟩
    | initial root word => simp [LiteralTranscript.valid, hm] at hv
    | payload bytes => simp [LiteralTranscript.valid, hm] at hv
    | c2 b word => simp [LiteralTranscript.valid, hm] at hv
  obtain ⟨root0, word0, h0⟩ := hshape0
  obtain ⟨b2o, w2o, h2⟩ := hshape2
  obtain ⟨b30o, w30o, h30⟩ := hshape30
  have hat2 := congrArg (fun pf : LiteralProtocol.Proof => pf 2) hproof
  have hmsg2 : Message.c2 b2a w2a = enrichMessage w (Message.c2 b2o w2o) := by
    calc
      Message.c2 b2a w2a = annotated.2.1.2 2 := ha2.symm
      _ = RawCutTranscriptRun.proof w original.2.1.2 2 := hat2
      _ = enrichMessage w (Message.c2 b2o w2o) := by
        change enrichMessage w (original.2.1.2 2) = _
        rw [h2]
  have hbytes2 : b2a = b2o := by
    injection hmsg2 with hbytes hword
  have hdecode2 : SemanticRecordCodec.decode ⟨2, by decide⟩ b2o.val =
      some ⟨.c2Root r2, by rfl⟩ := by rw [← hbytes2]; exact hdecode2a
  have hat30 := congrArg (fun pf : LiteralProtocol.Proof => pf 30) hproof
  have hmsg30 : Message.second b30a w30a = enrichMessage w (Message.second b30o w30o) := by
    calc
      Message.second b30a w30a = annotated.2.1.2 30 := ha30.symm
      _ = RawCutTranscriptRun.proof w original.2.1.2 30 := hat30
      _ = enrichMessage w (Message.second b30o w30o) := by
        change enrichMessage w (original.2.1.2 30) = _
        rw [h30]
  have hbytes30 : b30a = b30o := by
    injection hmsg30 with hbytes hword
  have hdecode30 : OpeningRecordCodec.decode .second b30o.val = some payload30 := by
    rw [← hbytes30]
    exact hdecode30a
  refine ⟨hvalid, htag, ?_⟩
  exact ⟨root0, word0, b2o, w2o, r2, b30o, w30o, payload30,
    h0, h2, h30, hdecode2, hdecode30⟩

#print axioms checks_imply_injection_format
end AspisR1.RawChecksInjectionFormat
end
