import RawCutProverCompiler
import OracleProgramReplay

/-! A concrete pure constructor for the compiler's word metadata. It rebuilds
the literal transcript from the recorded oracle answers, obtains the three
actual commitment-chain inputs, parses their roots, and recovers the packed
maps from the corresponding first-read cuts. No external oracle is supplied
to the constructor. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCutWordsFromView

open FS FS2 FS2.Duplex
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CanonicalCutEnrichedTranscript RawCutTranscriptRun RawCutProverCompiler

/-- Total on malformed proof data; for every selected round the sampler's
first cell exists, so this fallback is not used. -/
def frame (decoder : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : RawCutProverCompiler.Public) (pf : RawCutProverCompiler.Proof) (i : Nat) : Bytes :=
  (firstCell ((LiteralByteProtocol.protocol decoder).chain H pub pf i)).getD []

def frameFromView (decoder : LiteralByteProtocol.Decoder) (v : RunView) (i : Nat) : Bytes :=
  frame decoder (OracleProgramReplay.oracleOf v.1) v.2.1.1 v.2.1.2 i

def rootFrom (j : Fin 11) (input : Bytes) : State :=
  (RawByteCollisionTargets.pred j input).getD default

/-- Round 0 commits C1, round 2 commits C2, and round 30 commits the final
folded word. The roots occupy the two trailing fields and offset 38. -/
def buildWords (decoder : LiteralByteProtocol.Decoder) (v : RunView) : Words :=
  let f0 := frameFromView decoder v 0
  let f2 := frameFromView decoder v 2
  let f30 := frameFromView decoder v 30
  wordsFromRawCuts v.1 f0 f2 f30 (rootFrom 8 f0) (rootFrom 8 f2) (rootFrom 9 f30)

theorem verifier_reads_in_experiment (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State)
    (a : Bytes)
    (ha : a ∈ (eval H (verifier decoder d
      (eval H (experiment P (verifier decoder d))).2.1.1
      (eval H (experiment P (verifier decoder d))).2.1.2)).1.map Prod.fst) :
    a ∈ (eval H (experiment P (verifier decoder d))).1.map Prod.fst := by
  rw [RawCutProverCompiler.experiment_eval] at ha ⊢
  simp only [List.map_append]
  exact List.mem_append.mpr (Or.inr ha)

theorem recorded_transcript_eq (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State)
    (i : Nat) (hi : i ≤ 33) :
    let v := eval H (experiment P (verifier decoder d))
    (LiteralByteProtocol.protocol decoder).transcript
        (OracleProgramReplay.oracleOf v.1) v.2.1.1 v.2.1.2 i =
      (LiteralByteProtocol.protocol decoder).transcript H v.2.1.1 v.2.1.2 i := by
  dsimp only
  apply OracleProgramReplay.transcript_eq_of_agrees
    (LiteralByteProtocol.protocol decoder) (decisionOnBytes d) H
  · intro a ha
    exact OracleProgramReplay.oracleOf_eq H _ (FS.eval_consistent H _) a
      (verifier_reads_in_experiment decoder d P H a ha)
  · exact hi

theorem frameFromView_eq (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State)
    (i : Nat) (hi : i ≤ 33) :
    let v := eval H (experiment P (verifier decoder d))
    frameFromView decoder v i = frame decoder H v.2.1.1 v.2.1.2 i := by
  dsimp only [frameFromView, frame, Protocol.chain]
  rw [recorded_transcript_eq decoder d P H i hi]

private theorem firstCell_mem (H : Bytes → State)
    (s : Sampler Bytes State LiteralTranscript.Challenge) (a : Bytes)
    (ha : firstCell s = some a) : a ∈ (eval H s.toProgram).1.map Prod.fst := by
  cases s with
  | done c => cases ha
  | ask i k =>
      simp only [FS2.firstCell, Option.some.injEq] at ha
      subst i
      exact List.mem_cons_self ..
  | multi c cs nd k =>
      simp only [FS2.firstCell, Option.some.injEq] at ha
      subst c
      exact List.mem_cons_self ..

theorem frame_read (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State)
    (i : Nat) (hi : i < 33) :
    let v := eval H (experiment P (verifier decoder d))
    Read v.1 (frame decoder H v.2.1.1 v.2.1.2 i) := by
  dsimp only
  apply verifier_reads_in_experiment decoder d P H
  apply FS2.verifier_reads (LiteralByteProtocol.protocol decoder) (decisionOnBytes d)
    H _ _ i hi
  apply firstCell_mem
  have hbounded : firstCell (LiteralTranscript.samp i
      ((LiteralByteProtocol.protocol decoder).transcript H
        (eval H (experiment P (verifier decoder d))).2.1.1
        (eval H (experiment P (verifier decoder d))).2.1.2 i)
      ((LiteralByteProtocol.protocol decoder).msg
        (eval H (experiment P (verifier decoder d))).2.1.2 i)) ≠ none :=
    UnifiedSampler.firstCell_some _ _ _ _ _
  have hmap {I J A C : Type} [DecidableEq I] [Inhabited A]
      (label : I → J) (s : Sampler I A C) :
      firstCell (ProgramSamplerMap.map label s) = (firstCell s).map label := by
    cases s <;> rfl
  have hn : firstCell ((LiteralByteProtocol.protocol decoder).chain H
      (eval H (experiment P (verifier decoder d))).2.1.1
      (eval H (experiment P (verifier decoder d))).2.1.2 i) ≠ none := by
    change firstCell (ProgramSamplerMap.map Addr.toBytes _) ≠ none
    rw [hmap]
    simpa using hbounded
  unfold frame
  cases h : firstCell ((LiteralByteProtocol.protocol decoder).chain H
      (eval H (experiment P (verifier decoder d))).2.1.1
      (eval H (experiment P (verifier decoder d))).2.1.2 i) with
  | none => exact False.elim (hn h)
  | some a => rfl

/-- The pure constructor selects exactly the actual oracle run's commitment
cuts, with no hypothesis that supplied metadata already equals a recovered word. -/
theorem buildWords_eq_actual_cuts (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    let v := eval H (experiment P (verifier decoder d))
    let f0 := frame decoder H v.2.1.1 v.2.1.2 0
    let f2 := frame decoder H v.2.1.1 v.2.1.2 2
    let f30 := frame decoder H v.2.1.1 v.2.1.2 30
    buildWords decoder v =
      wordsFromRawCuts v.1 f0 f2 f30 (rootFrom 8 f0) (rootFrom 8 f2) (rootFrom 9 f30) := by
  dsimp only [buildWords]
  rw [frameFromView_eq decoder d P H 0 (by decide),
    frameFromView_eq decoder d P H 2 (by decide),
    frameFromView_eq decoder d P H 30 (by decide)]

/-- For parsed commitment frames, one already-budgeted collision exclusion
identifies all three constructed words with the full recorded recovery maps.
The remaining parser premises are explicit source-format obligations. -/
theorem buildWords_eq_full (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State)
    (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable (eval H (experiment P (verifier decoder d))).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q)
      emptyTable (eval H (experiment P (verifier decoder d))).1)
    (roots : Fin 3 → State)
    (h0 : let v := eval H (experiment P (verifier decoder d))
      RawByteCollisionTargets.pred 8 (frame decoder H v.2.1.1 v.2.1.2 0) = some (roots 0))
    (h2 : let v := eval H (experiment P (verifier decoder d))
      RawByteCollisionTargets.pred 8 (frame decoder H v.2.1.1 v.2.1.2 2) = some (roots 1))
    (h30 : let v := eval H (experiment P (verifier decoder d))
      RawByteCollisionTargets.pred 9 (frame decoder H v.2.1.1 v.2.1.2 30) = some (roots 2)) :
    let v := eval H (experiment P (verifier decoder d))
    buildWords decoder v = wordsFromMaps (fullC1Map v.1 (roots 0))
      (fullC2Map v.1 (roots 1)) (fullFoldedMap v.1 (roots 2)) := by
  dsimp only at h0 h2 h30 ⊢
  rw [buildWords_eq_actual_cuts]
  simp only [rootFrom, h0, h2, h30, Option.getD_some]
  exact wordsFromRawCuts_eq_full iv H _ Q (FS.eval_consistent H _) hQ hout
    _ _ _ _ _ _ 8 8 9
    (frame_read decoder d P H 0 (by decide))
    (frame_read decoder d P H 2 (by decide))
    (frame_read decoder d P H 30 (by decide)) h0 h2 h30

#print axioms recorded_transcript_eq
#print axioms frameFromView_eq
#print axioms frame_read
#print axioms buildWords_eq_actual_cuts
#print axioms buildWords_eq_full
end AspisR1.RawCutWordsFromView
end
