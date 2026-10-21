import OraclePortWords
import RawChecksConstructorScheduleV4
import RawCompiledTranscriptRoundAlignmentV7
import R1LiteralByteRunFacts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.OraclePortSchedule
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.RawCutProverCompiler (Prover RunView experiment)
open AspisR1.RawCutTranscriptRun
open OracleDecisionFeasibilityCore (Decision verifier)
open OracleDecisionFeasibilityCompiler (compiled compiled_experiment_eval)
open AspisR1.RawCutWordsFromView AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.LiteralTranscript

abbrev Bytes := AspisV8R19.DuplexFrames.Bytes
abbrev State := AspisV8R19.SourceDuplexStep.State
attribute [local irreducible] BinCompiledRunWordStability.wordsFromRun

def originalRun (decoder : LiteralByteProtocol.Decoder)
    (d : Decision) (P : Prover) (H : Bytes → State) : RunView :=
  eval H (experiment P (verifier decoder d))

def annotatedRun (decoder : LiteralByteProtocol.Decoder)
    (d : Decision) (P : Prover) (H : Bytes → State) : RunView :=
  eval H (experiment (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
    (verifier decoder d))


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

theorem checks_force_original_constructor_schedule
    (decoder : LiteralByteProtocol.Decoder)
    (d : Decision) (P : Prover) (H : Bytes → State)
    (original annotated : RunView)
    (horiginal : original = eval H (experiment P (verifier decoder d)))
    (hannotated : annotated = eval H (experiment
      (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P) (verifier decoder d)))
    (checks : LiteralAcceptanceTerminal.Checks annotated.2.1.1
      (((LiteralByteProtocol.protocol decoder).transcript H
        annotated.2.1.1 annotated.2.1.2 33).rounds)) :
    ∀ i, i ≤ 30 → LiteralTranscript.valid i (original.2.1.2 i) := by
  let w := BinCompiledRunWordStability.wordsFromRun decoder original
  let extendRun : RunView → RunView := fun v =>
    (v.1 ++ (eval H (verifier decoder d v.2.1.1 v.2.1.2)).1,
      ((v.2.1.1, RawCutTranscriptRun.proof
        (BinCompiledRunWordStability.wordsFromRun decoder v) v.2.1.2), v.2.2))
  have hext : eval H (experiment
      (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P) (verifier decoder d)) =
      extendRun (eval H (experiment P (verifier decoder d))) := by
    change eval H (experiment
      (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P) (verifier decoder d)) = _
    simpa only [extendRun] using
      (compiled_experiment_eval decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P H)
  have hextOriginal : extendRun original =
      extendRun (eval H (experiment P (verifier decoder d))) := congrArg extendRun horiginal
  have hrun : annotated =
      let v := original
      (v.1 ++ (eval H (verifier decoder d v.2.1.1 v.2.1.2)).1,
        ((v.2.1.1, RawCutTranscriptRun.proof w v.2.1.2), v.2.2)) := by
    calc
      annotated = eval H (experiment
          (compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) P)
          (verifier decoder d)) := hannotated
      _ = extendRun (eval H (experiment P (verifier decoder d))) := hext
      _ = extendRun original := hextOriginal.symm
      _ = _ := rfl
  have hproof : annotated.2.1.2 = RawCutTranscriptRun.proof w original.2.1.2 :=
    congrArg (fun v : RunView => v.2.1.2) hrun
  have hlenAnnotated :
      ((LiteralByteProtocol.protocol decoder).transcript H annotated.2.1.1
        annotated.2.1.2 33).rounds.length = 33 :=
    LiteralByteRunFacts.transcript_round decoder H annotated.2.1.1
      annotated.2.1.2 33
  have hvalid := RawChecksConstructorSchedule.checks_force_constructor_schedule
    annotated.2.1.1
    ((LiteralByteProtocol.protocol decoder).transcript H annotated.2.1.1
      annotated.2.1.2 33).rounds
    checks (by omega)
  intro i hi
  have hi33 : i < 33 := by omega
  obtain ⟨m, c, hcompiled, hv⟩ := hvalid i hi
  have hentry := LiteralByteRunFacts.transcript_index decoder H annotated.2.1.1
    annotated.2.1.2 33 i hi33
  have hp : (m, c) =
      (annotated.2.1.2 i,
        (eval H (LiteralByteSampler.samp i
          ((LiteralByteProtocol.protocol decoder).transcript H annotated.2.1.1
            annotated.2.1.2 i) (annotated.2.1.2 i)).toProgram).2) :=
    Option.some.inj (hcompiled.symm.trans hentry)
  have hm : m = annotated.2.1.2 i := congrArg Prod.fst hp
  have hv' : LiteralTranscript.valid i (annotated.2.1.2 i) := by
    simpa only [hm] using hv
  have hproofAt := congrArg (fun pf : LiteralProtocol.Proof => pf i) hproof
  have hmessage : annotated.2.1.2 i = enrichMessage w (original.2.1.2 i) := by
    simpa only [RawCutTranscriptRun.proof] using hproofAt
  have hvEnriched : LiteralTranscript.valid i (enrichMessage w (original.2.1.2 i)) := by
    simpa only [hmessage] using hv'
  exact (valid_enrichMessage w i (original.2.1.2 i)).mp hvEnriched

#print axioms valid_enrichMessage
#print axioms checks_force_original_constructor_schedule
end AspisR1.OraclePortSchedule
end
