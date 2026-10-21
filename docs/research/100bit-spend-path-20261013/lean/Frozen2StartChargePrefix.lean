import OraclePortFrozen2Consumer
import OracleProgramLawExt

/-! The charged experiment stops before terminal reads. Its proof metadata
is computed from the same causal cuts as the adopted full experiment. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Frozen2StartChargePrefix
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
open OraclePortFrozen2Consumer

abbrev prover (P : Prover) := OraclePortStoredProjectionC4.project (canon P)
abbrev base (D : LiteralByteProtocol.Decoder) (P : Prover) :=
  RawCutProverCompiler.experiment (prover P) (RawCutProverCompiler.verifier D (fun _ _ => true))

def charged (D : LiteralByteProtocol.Decoder) (P : Prover) :
    RawRecordedOracleExtractionMassBin.Experiment :=
  bind (RawCutProverCompiler.compiled D (fun _ _ => true)
    (BinCompiledRunWordStability.wordsFromRun D) (prover P)) fun i => .done (i,true)

theorem charged_eval (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    eval H (charged D P) =
      ((eval H (base D P)).1,
        (((eval H (base D P)).2.1.1, RawCutTranscriptRun.proof
          (BinCompiledRunWordStability.wordsFromRun D (eval H (base D P)))
          (eval H (base D P)).2.1.2),true)) := by
  simp only [charged,eval_bind,RawCutProverCompiler.eval_compiled,eval,List.append_nil,base]

theorem prover_eval (P : Prover) (H : Bytes → State) :
    eval H (prover P) = ((eval H P).1,
      ((eval H P).2.statement,R16CanonReduction.proof (eval H P).2.proof)) := by
  rw [prover,OraclePortStoredProjectionC4.project_eval,canon_eval]
  rfl

theorem fibre_prover (s : Bytes) (P : Prover) :
    OraclePortStoredReductionC7.pairProver s P = prover P := by
  unfold OraclePortStoredReductionC7.pairProver prover
    OraclePortStoredProjectionC4.project canon OraclePortStoredReductionC7.fixStored
  induction P with
  | done i => rfl
  | ask a k ih =>
    simp only [AspisV8R19.OracleProgramOps.bind]
    congr 1
    funext v
    exact ih v

/-- Full and charged outputs have exactly the same submitted transcript.
No probability distribution is replaced by a fixed stored-input fibre. -/
theorem same_transcript (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    (eval H (projected D P)).2.1 = (eval H (charged D P)).2.1 := by
  rw [projected_eval,OraclePortStoredReductionC7.annotated_selected,fibre_prover]
  change (eval H (OracleDecisionPrereqStarts.annotated D _ _ (prover P))).2.1 = _
  rw [OracleDecisionPrereqStarts.annotated,OracleDecisionFeasibilityCompiler.compiled_experiment_eval,
    charged_eval]
  dsimp only
  change ((eval H (OraclePortExperiment.original D (dV (eval H P).2.stored) (prover P))).2.1.1,
    RawCutTranscriptRun.proof (BinCompiledRunWordStability.wordsFromRun D
      (eval H (OraclePortExperiment.original D (dV (eval H P).2.stored) (prover P))))
      (eval H (OraclePortExperiment.original D (dV (eval H P).2.stored) (prover P))).2.1.2) = _
  rw [OraclePortSamplerPrefixDraft.words_prefix,OraclePortSamplerPrefixDraft.output_pair]

/-- Chronological causality: all reads of the charged experiment precede
all terminal Merkle reads in the first pass of the actual recorded run. -/
theorem chronological_prefix (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    ∃ tail, (eval H (projected D P)).1 = (eval H (charged D P)).1 ++ tail := by
  rw [projected_eval,OraclePortStoredReductionC7.annotated_selected,fibre_prover]
  change ∃ tail, (eval H (OracleDecisionPrereqStarts.annotated D _ _ (prover P))).1 = _
  rw [OracleDecisionPrereqStarts.annotated,OracleDecisionFeasibilityCompiler.compiled_experiment_eval,
    charged_eval]
  dsimp only
  change ∃ tail, (eval H (OraclePortExperiment.original D (dV (eval H P).2.stored)
    (prover P))).1 ++ _ = (eval H (base D P)).1 ++ tail
  rw [OraclePortSamplerPrefixDraft.split_trace,List.append_assoc]
  exact ⟨_,rfl⟩

/-- A start already followed in the charged cannot first occur in the terminal
suffix. This preserves the actual first index, including prover duplicates. -/
theorem first_start_before_terminal (D : LiteralByteProtocol.Decoder) (P : Prover)
    (H : Bytes → State) (a : Bytes) (ha : Read (eval H (charged D P)).1 a) :
    firstIdx a (eval H (projected D P)).1 = firstIdx a (eval H (charged D P)).1 := by
  obtain ⟨tail,he⟩ := chronological_prefix D P H
  rw [he]
  exact OracleProgramRecording.firstIdx_append_of_read a _ tail ha

theorem starts (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (charged D P)).1 ≤ Q+34 := by
  rw [charged_eval]
  unfold base
  rw [RawCutProverCompiler.experiment_eval,
    DecodedFirstReadUnionBound.decoderFirstReads_append]
  have hp := DecoderQueryAccounting.starts_le_queries RecordedBinaryExperimentBin.dec
    emptyTable (eval H (prover P)).1
  have hlen : (eval H (prover P)).1.length ≤ Q := by rw [prover_eval]; exact hq H
  exact Nat.add_le_add (hp.trans hlen) (BinHonestQueryBudget.verifier_starts D
    (fun _ _ => true) H _ _ _)

/-- Every submitted transcript chain starts in the sampler charged, whether
or not the prover already read that address. In particular no accepted
transcript start can be first-read only in the terminal suffix. -/
theorem transcript_start_read (D : LiteralByteProtocol.Decoder) (P : Prover)
    (H : Bytes → State) (n : Nat) (hn : n < 33) (a : Bytes)
    (ha : firstCell ((LiteralByteProtocol.protocol D).chain H
      (eval H (projected D P)).2.1.1 (eval H (projected D P)).2.1.2 n) = some a) :
    Read (eval H (charged D P)).1 a := by
  rw [same_transcript,charged_eval] at ha
  dsimp only at ha
  rw [RawCutTranscriptRun.chain_eq] at ha
  have he : RawCutWordsFromView.frame D H (eval H (base D P)).2.1.1
      (eval H (base D P)).2.1.2 n = a := by
    unfold RawCutWordsFromView.frame
    rw [ha]
    rfl
  rw [charged_eval,← he]
  exact RawCutWordsFromView.frame_read D (fun _ _ => true) (prover P) H n hn

/-- The requested dichotomy as actual address membership: a submitted
transcript start occurs in the prover log or the verifier's followed log. -/
theorem transcript_start_prover_or_followed (D : LiteralByteProtocol.Decoder) (P : Prover)
    (H : Bytes → State) (n : Nat) (hn : n < 33) (a : Bytes)
    (ha : firstCell ((LiteralByteProtocol.protocol D).chain H
      (eval H (projected D P)).2.1.1 (eval H (projected D P)).2.1.2 n) = some a) :
    Read (eval H P).1 a ∨ Read
      (eval H (RawCutProverCompiler.verifier D (fun _ _ => true)
        (eval H (prover P)).2.1 (eval H (prover P)).2.2)).1 a := by
  have hr := transcript_start_read D P H n hn a ha
  rw [charged_eval] at hr
  unfold base at hr
  rw [RawCutProverCompiler.experiment_eval] at hr
  change a ∈ (_ ++ _ : List (Bytes × State)).map Prod.fst at hr
  rw [List.map_append,List.mem_append] at hr
  rcases hr with hp | hv
  · apply Or.inl
    change a ∈ (eval H P).1.map Prod.fst
    simpa only [prover_eval] using hp
  · apply Or.inr
    exact hv

/-- The observable reads only the charged charged, reconstructed from the
full record. Its fallback oracle values are never used. -/
def recovered (D : LiteralByteProtocol.Decoder) (P : Prover)
    (run : RawCutProverCompiler.RunView) : RawCutProverCompiler.RunView :=
  eval (OracleProgramReplay.oracleOf run.1) (charged D P)

theorem recovered_eval (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    recovered D P (eval H (projected D P)) = eval H (charged D P) := by
  apply OracleProgramReplay.eval_oracleOf H _ _ (FS.eval_consistent H _)
  obtain ⟨tail,he⟩ := chronological_prefix D P H
  intro a ha
  rw [he,List.map_append]
  exact List.mem_append_left _ ha

#print axioms charged_eval
#print axioms prover_eval
#print axioms fibre_prover
#print axioms same_transcript
#print axioms chronological_prefix
#print axioms first_start_before_terminal
#print axioms starts
#print axioms transcript_start_read
#print axioms transcript_start_prover_or_followed
#print axioms recovered_eval
end AspisR1.Frozen2StartChargePrefix
end
