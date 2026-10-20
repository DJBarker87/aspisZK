import RWireRawAdaptiveCompiledCompletion
import RWireCheckedFormat
import RWireInitialTag
import RecordedBinaryExperimentBin

set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireCompletion
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler RawCutTranscriptRun RecordedBinaryExperimentBin

/-- The only residual public-selection law, restricted to its actual domain. -/
def InitialTag (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat) : Prop :=
  ∀ H : Bytes → State, ¬ binaryCollision Q (eval H (recorded D d P)) →
    FS2.accepts (eval H (recorded D d P)) →
    LiteralTranscript.valid 0 ((eval H (recorded D d P)).2.1.2 0) →
    (eval H (recorded D d P)).2.1.1.tag = 2

/-- Full completion already implies the residual law; nothing is strengthened. -/
theorem initialTag_of_completion (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (hc : BinaryCompletion D d P Q) : InitialTag D d P Q := by
  intro H hout ha hv
  let run := eval H (recorded D d P)
  cases hm : run.2.1.2 0 with
  | payload b => simp [run, hm, LiteralTranscript.valid] at hv
  | c2 b w => simp [run, hm, LiteralTranscript.valid] at hv
  | second b w => simp [run, hm, LiteralTranscript.valid] at hv
  | initial root word =>
    have hf : firstCell ((LiteralByteProtocol.protocol D).chain H run.2.1.1 run.2.1.2 0) =
        some (PublicInitFrame.frame run.2.1.1.pubBytes root) := by
      change firstCell (LiteralByteSampler.samp 0 _ (run.2.1.2 0)) = _
      rw [hm]
      exact RawCutCommitmentFrames.first_initial _ root word
    obtain ⟨own,pend,g,hd,hfollow⟩ := hc H hout ha 0 _ (by change 0 < 33; decide) hf
    have ht := RWireInitialTag.initial_follow_tag run.2.1.1 root
      (tableBefore emptyTable run.1 _) (traceFrom run.1 _) own pend g _ hd hfollow
    exact ht

/-- Symbolic binary completion. No successful opening or path-recomputation
premise: total recovery, including `none`, agrees with compiler metadata. -/
theorem completion_of_format (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (hQ : ∀ H, firstReads emptyTable (eval H (original D d P)).1 ≤ Q)
    (hformat : ∀ H, FS2.accepts (eval H (original D d P)) →
      RWireCheckedFormat.Format (eval H (original D d P)).2.1.2)
    (htag : InitialTag D d P Q) : BinaryCompletion D d P Q := by
  intro H hout ha n a hn hf
  let orig := eval H (original D d P)
  let run := eval H (recorded D d P)
  have he : run = (orig.1 ++ (eval H (verifier D d orig.2.1.1 orig.2.1.2)).1,
      ((orig.2.1.1, proof (BinCompiledRunWordStability.wordsFromRun D orig) orig.2.1.2), orig.2.2)) :=
    compiled_experiment_eval D d (BinCompiledRunWordStability.wordsFromRun D) P H
  have haorig : FS2.accepts orig := by
    change run.2.2 = true at ha
    change orig.2.2 = true
    rw [he] at ha
    exact ha
  obtain ⟨hvalid, r1,w1,b2,w2,r2,b30,w30,v30,h0,h2,h30,hp2,hp30⟩ := hformat H haorig
  have hv0 : LiteralTranscript.valid 0 (run.2.1.2 0) := by
    rw [he]
    exact (RWireCheckedFormat.valid_enrich _ _ _).mpr (hvalid 0 (by decide))
  have htagorig : orig.2.1.1.tag = 2 := by
    have h := htag H hout ha hv0
    change run.2.1.1.tag = 2 at h
    rw [he] at h
    exact h
  have houtorig : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable orig.1 := by
    intro hh
    apply hout
    change hitsBad _ emptyTable run.1
    rw [he]
    exact TraceAppend.hitsBad_of_prefix _ _ _ _ hh
  have hb := RWireRawAdaptiveCompiledCompletion.actual_compiled_transcript
    D d P H Q (hQ H) houtorig hvalid htagorig r1 w1 b2 w2 r2 b30 w30 v30
    h0 h2 h30 hp2 hp30 n hn
  have houtpair : run.2.1 = RWireRawCompiledTranscript.output D d P H := by
    change (eval H (experiment (compiled D d (BinCompiledRunWordStability.wordsFromRun D) P)
      (verifier D d))).2.1 = _
    rw [RawCutProverCompiler.experiment_eval]
    rfl
  have hframe : RWireRawCompiledTranscript.output D d P H = run.2.1 := houtpair.symm
  dsimp only at hb
  rw [hframe] at hb
  have hraw : RawCutWordsFromView.frame D H run.2.1.1 run.2.1.2 n = a := by
    unfold RawCutWordsFromView.frame
    rw [hf]
    rfl
  rw [hraw] at hb
  exact hb

/-- With the already-required checked format, this is the exact remaining
condition on the decision; all decoding and follow work has been proved. -/
theorem completion_iff_initialTag (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (hQ : ∀ H, firstReads emptyTable (eval H (original D d P)).1 ≤ Q)
    (hformat : ∀ H, FS2.accepts (eval H (original D d P)) →
      RWireCheckedFormat.Format (eval H (original D d P)).2.1.2) :
    BinaryCompletion D d P Q ↔ InitialTag D d P Q :=
  ⟨initialTag_of_completion D d P Q, completion_of_format D d P Q hQ hformat⟩

#print axioms initialTag_of_completion
#print axioms completion_of_format
#print axioms completion_iff_initialTag
end AspisR1.RWireCompletion
end
