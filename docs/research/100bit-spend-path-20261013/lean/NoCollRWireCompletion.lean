import RWireCompletion
set_option autoImplicit false
noncomputable section
namespace AspisR1.NoCollRWireCompletion
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler RawCutTranscriptRun RecordedBinaryExperimentBin
open RWireCompletion

/-- Symbolic binary completion. No successful opening or path-recomputation
premise: total recovery, including `none`, agrees with compiler metadata. -/
theorem completion_of_format (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (hQ : ∀ H, firstReads emptyTable (eval H (original D d P)).1 ≤ Q)
    (hformat : ∀ H, ¬ binaryCollision Q (eval H (recorded D d P)) →
      FS2.accepts (eval H (original D d P)) →
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
  obtain ⟨hvalid, r1,w1,b2,w2,r2,b30,w30,v30,h0,h2,h30,hp2,hp30⟩ := hformat H hout haorig
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


#print axioms completion_of_format
end AspisR1.NoCollRWireCompletion
end
