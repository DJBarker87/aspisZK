import OraclePortWords
import RWireRawFullPublicRun
import RWireCheckedFormat
import R1FollowAppend

/-! Decoder completion is transported from the sampler prefix across arbitrary
terminal bytes. No canonical-address assertion is made about terminal reads. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortSamplerPrefixDraft
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler (Prover RunView)
open OraclePortExperiment (Decision original recorded)
open RawCutWordsFromView (frame frameFromView)

abbrev base (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) : RunView :=
  eval H (RawCutProverCompiler.experiment P (RawCutProverCompiler.verifier D (fun _ _ => true)))

abbrev terminal (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) :=
  (eval H (OracleDecisionFeasibilityCore.onBytes d
    ((LiteralByteProtocol.protocol D).transcript H (eval H P).2.1 (eval H P).2.2 33)
    ((eval H P).2.2 33))).1

theorem split_trace (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) :
    (eval H (original D d P)).1 = (base D P H).1 ++ terminal D d P H := by
  rw [original,OracleDecisionFeasibilityCore.original,RawCutProverCompiler.experiment_eval,
    OracleDecisionFeasibilityBudget.verifier_eval]
  unfold base
  rw [RawCutProverCompiler.experiment_eval,RawCutProverCompiler.verifier,FS2.verifier_eval]
  simp only [List.append_assoc]
  rfl

theorem output_pair (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) :
    (eval H (original D d P)).2.1 = (base D P H).2.1 := by
  rw [original,OracleDecisionFeasibilityCore.original,RawCutProverCompiler.experiment_eval]
  unfold base
  rw [RawCutProverCompiler.experiment_eval]

theorem words_prefix (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) :
    BinCompiledRunWordStability.wordsFromRun D (eval H (original D d P)) =
      BinCompiledRunWordStability.wordsFromRun D (base D P H) := by
  have hf (n : Nat) (hn : n < 33) :
      frameFromView D (eval H (original D d P)) n = frameFromView D (base D P H) n := by
    rw [OraclePortReplay.frameFromView_eq D d P H n (by omega),
      RawCutWordsFromView.frameFromView_eq D (fun _ _ => true) P H n (by omega)]
    rw [output_pair]
  have hc (n : Nat) (hn : n < 33) :
      BinRawByteCutRecovery.cut (eval H (original D d P)).1 (frameFromView D (base D P H) n) =
        BinRawByteCutRecovery.cut (base D P H).1 (frameFromView D (base D P H) n) := by
    rw [split_trace]
    apply OracleProgramRecording.cut_append_of_read
    rw [RawCutWordsFromView.frameFromView_eq D (fun _ _ => true) P H n (by omega)]
    exact RawCutWordsFromView.frame_read D (fun _ _ => true) P H n hn
  unfold BinCompiledRunWordStability.wordsFromRun
  rw [hf 0 (by decide),hf 2 (by decide),hf 30 (by decide)]
  unfold BinCanonicalCutWords.wordsFromRawCuts BinCanonicalCutWords.rawC1Map
    BinCanonicalCutWords.rawC2Map BinCanonicalCutWords.rawFoldedMap
  dsimp only
  rw [hc 0 (by decide),hc 2 (by decide),hc 30 (by decide)]

/-- A completion theorem on the original generalized trace. Format and tag
are syntax checks, not completion hypotheses; the terminal itself is arbitrary. -/
theorem original_decodes (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) (Q : Nat)
    (hQ : firstReads emptyTable (eval H (original D d P)).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable (eval H (original D d P)).1)
    (format : RWireCheckedFormat.Format (eval H (original D d P)).2.1.2)
    (tag : (eval H (original D d P)).2.1.1.tag = 2) (n : Nat) (hn : n < 33) :
    let run := eval H (original D d P)
    let raw := frame D H run.2.1.1 run.2.1.2 n
    ∃ own pend g,
      RecordedBinaryExperimentBin.dec raw (tableBefore emptyTable run.1 raw) = some (own,pend,g) ∧
      bfollow g (traceFrom run.1 raw) own pend (tableBefore emptyTable run.1 raw) =
        some (CanonicalCutEnrichedTranscript.enrichPrefix
          (BinCompiledRunWordStability.wordsFromRun D run)
          ((LiteralByteProtocol.protocol D).transcript H run.2.1.1 run.2.1.2 n),
          CanonicalCutEnrichedTranscript.enrichMessage
            (BinCompiledRunWordStability.wordsFromRun D run) (run.2.1.2 n),
          (LiteralByteProtocol.protocol D).chal H run.2.1.1 run.2.1.2 n) := by
  have hQB : firstReads emptyTable (base D P H).1 ≤ Q :=
    (TraceAppend.firstReads_le_append _ _ (terminal D d P H)).trans
      (by simpa only [← split_trace D d P H] using hQ)
  have hOB : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable (base D P H).1 := by
    intro hh
    apply hout
    rw [split_trace]
    exact TraceAppend.hitsBad_of_prefix _ _ _ _ hh
  rw [output_pair] at format tag
  obtain ⟨hv,r1,w1,b2,w2,r2,b30,w30,v30,h0,h2,h30,hp2,hp30⟩ := format
  have hb := RWireRawFullPublicRun.adaptive_run_decodes_and_follows D (fun _ _ => true)
    P H Q hQB hOB hv tag r1 w1 b2 w2 r2 b30 w30 v30 h0 h2 h30 hp2 hp30 n hn
  obtain ⟨own,pend,g,hd,hfollow⟩ := hb
  dsimp only
  rw [words_prefix,output_pair]
  let raw := frame D H (base D P H).2.1.1 (base D P H).2.1.2 n
  have hr : Read (base D P H).1 raw := RawCutWordsFromView.frame_read D
    (fun _ _ => true) P H n hn
  refine ⟨own,pend,g,?_,?_⟩
  · rw [split_trace,TraceAppend.tableBefore_append _ _ _ _ hr]
    exact hd
  · rw [split_trace,TraceAppend.tableBefore_append _ _ _ _ hr,
      TraceAppend.traceFrom_append _ _ _ hr]
    exact FollowAppend.bfollow_append_of_some g _ _ own pend _ _ hfollow

#print axioms split_trace
#print axioms output_pair
#print axioms words_prefix
#print axioms original_decodes
end AspisR1.OraclePortSamplerPrefixDraft
end
