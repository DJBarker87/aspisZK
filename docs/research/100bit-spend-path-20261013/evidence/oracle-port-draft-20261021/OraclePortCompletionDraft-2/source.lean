import OraclePortSamplerPrefixDraft
import OraclePortConsumer
import OraclePortAdmission

set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCompletionDraft
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler (Prover RunView)
open OraclePortExperiment (Decision original recorded)
open RawCutWordsFromView (frame)
open CanonicalCutEnrichedTranscript (enrichPrefix enrichMessage)

/-- Ported completion on the new compiled trace. Only actual sampler formats
are inspected; arbitrary terminal reads remain unrestricted bytes. -/
theorem completion_of_format (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (Q : Nat)
    (hQ : ∀ H, firstReads emptyTable (eval H (original D d P)).1 ≤ Q)
    (hformat : ∀ H, ¬ RecordedBinaryExperimentBin.binaryCollision Q
      (eval H (recorded D d P)) → FS2.accepts (eval H (original D d P)) →
      RWireCheckedFormat.Format (eval H (original D d P)).2.1.2)
    (htag : ∀ H, FS2.accepts (eval H (original D d P)) →
      (eval H (original D d P)).2.1.1.tag = 2) :
    OraclePortConsumer.Completion D d P Q := by
  intro H hout ha n a hn hfirst
  let orig := eval H (original D d P)
  let run := eval H (recorded D d P)
  let W := BinCompiledRunWordStability.wordsFromRun D orig
  let tail := (eval H (OraclePortExperiment.verifier D d orig.2.1.1 orig.2.1.2)).1
  have he : run = (orig.1 ++ tail,((orig.2.1.1,RawCutTranscriptRun.proof W orig.2.1.2),orig.2.2)) :=
    OracleDecisionFeasibilityCompiler.compiled_experiment_eval D d
      (BinCompiledRunWordStability.wordsFromRun D) P H
  have haorig : FS2.accepts orig := by
    change run.2.2 = true at ha
    change orig.2.2 = true
    rw [he] at ha
    exact ha
  have ho : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable orig.1 := by
    intro hh
    apply hout
    change hitsBad _ emptyTable run.1
    rw [he]
    exact TraceAppend.hitsBad_of_prefix _ _ _ _ hh
  obtain ⟨own,pend,g,hd,hf⟩ := OraclePortSamplerPrefixDraft.original_decodes
    D d P H Q (hQ H) ho (hformat H hout haorig) (htag H haorig) n hn
  let raw := frame D H orig.2.1.1 orig.2.1.2 n
  have hr : Read orig.1 raw := OraclePortReplay.frame_read D d P H n hn
  have hraw : raw = a := by
    change firstCell ((LiteralByteProtocol.protocol D).chain H run.2.1.1 run.2.1.2 n) = some a at hfirst
    rw [he] at hfirst
    dsimp only at hfirst
    rw [RawCutTranscriptRun.chain_eq] at hfirst
    unfold raw frame
    rw [hfirst]
    rfl
  have hd' : RecordedBinaryExperimentBin.dec raw
      (tableBefore emptyTable run.1 raw) = some (own,pend,g) := by
    rw [he,TraceAppend.tableBefore_append _ _ _ _ hr]
    exact hd
  have hf' : bfollow g (traceFrom run.1 raw) own pend (tableBefore emptyTable run.1 raw) =
      some (enrichPrefix W ((LiteralByteProtocol.protocol D).transcript H orig.2.1.1 orig.2.1.2 n),
        enrichMessage W (orig.2.1.2 n),(LiteralByteProtocol.protocol D).chal H orig.2.1.1 orig.2.1.2 n) := by
    rw [he,TraceAppend.tableBefore_append _ _ _ _ hr,TraceAppend.traceFrom_append _ _ _ hr]
    exact FollowAppend.bfollow_append_of_some g _ _ own pend _ _ hf
  refine ⟨own,pend,g,?_,?_⟩
  · rw [← hraw]
    exact hd'
  · change bfollow g (traceFrom run.1 a) own pend (tableBefore emptyTable run.1 a) = _
    change bfollow g (traceFrom run.1 a) own pend (tableBefore emptyTable run.1 a) =
      some ((LiteralByteProtocol.protocol D).transcript H run.2.1.1 run.2.1.2 n,
        (LiteralByteProtocol.protocol D).msg run.2.1.2 n,
        (LiteralByteProtocol.protocol D).chal H run.2.1.1 run.2.1.2 n)
    rw [← hraw,hf',he]
    dsimp only
    rw [RawCutTranscriptRun.transcript_eq]
    congr 1
    congr 1
    change (LiteralByteProtocol.protocol D).chal H orig.2.1.1 orig.2.1.2 n =
      (LiteralByteProtocol.protocol D).chal H orig.2.1.1 (RawCutTranscriptRun.proof W orig.2.1.2) n
    unfold Protocol.chal
    rw [RawCutTranscriptRun.chain_eq]

/-- Typed acceptance already supplies syntax at compiled rows. Completion
is derived from that syntax, not taken as an independent premise. -/
theorem completion_of_checks (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (Q : Nat)
    (hQ : ∀ H, firstReads emptyTable (eval H (original D d P)).1 ≤ Q)
    (hchecks : OraclePortConsumer.CheckedAcceptance D d P Q)
    (htag : ∀ H, FS2.accepts (eval H (original D d P)) →
      (eval H (original D d P)).2.1.1.tag = 2) :
    OraclePortConsumer.Completion D d P Q := by
  apply completion_of_format D d P Q hQ _ htag
  intro H hout ha
  have checks := hchecks H hout ha
  have fmt := RWireCheckedFormat.format_of_checks D H
    (eval H (recorded D d P)).2.1.1 (eval H (recorded D d P)).2.1.2 checks
  unfold recorded OracleDecisionPrereqStarts.annotated at fmt
  rw [OracleDecisionFeasibilityCompiler.compiled_experiment_eval] at fmt
  exact RWireCheckedFormat.format_of_enrich _ _ fmt

#print axioms completion_of_format
#print axioms completion_of_checks
end AspisR1.OraclePortCompletionDraft
end
