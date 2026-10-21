import OraclePortAdmission
import OraclePortHeadline
import OracleDecisionMultiCompiledRecovery

/-! An admitted shared-multiproof kernel. Forests/frames are parameters, not
outputs of a claimed frozen parser. This is intentionally not named dV. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortMultiKernel
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler (Public Proof Prover RunView experiment)
open OraclePortExperiment (Decision verifier original recorded Budget)
open OracleDecisionMultiTree (Commitment Admissible)
open OraclePortAdmission (admit Guard)

abbrev decision (cs : List Commitment) (duplicates frames : List Bytes) : Decision :=
  admit (OracleDecisionMultiTree.decision cs duplicates frames)

theorem budget (cs : List Commitment) (duplicates frames : List Bytes)
    (ha : Admissible cs duplicates frames) : Budget (decision cs duplicates frames) := by
  apply OraclePortAdmission.admission_budget
  intro H p m
  have hc := OracleDecisionMultiTree.closed_count H cs duplicates frames ha
  have hb := OracleDecisionMultiTree.budget_bound cs duplicates frames ha
  change (eval H (OracleDecisionMultiTree.terminal cs duplicates frames)).1.length ≤ 1046
  omega

/-- Admission does not change the accepted core trace; it is a pure guard. -/
theorem admitted_verifier_eq (D : LiteralByteProtocol.Decoder) (core : Decision)
    (H : Bytes → State) (pub : Public) (pf : Proof)
    (hg : Guard (LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol D).transcript H pub pf 33))) :
    eval H (verifier D (admit core) pub pf) = eval H (verifier D core pub pf) := by
  rw [OracleDecisionFeasibilityBudget.verifier_eval,
    OracleDecisionFeasibilityBudget.verifier_eval]
  simp only [OracleDecisionFeasibilityCore.onBytes, admit, if_pos hg]

theorem admitted_original_eq (D : LiteralByteProtocol.Decoder) (core : Decision)
    (P : Prover) (H : Bytes → State)
    (ha : FS2.accepts (eval H (original D (admit core) P))) :
    eval H (original D (admit core) P) = eval H (original D core P) := by
  have hg := OraclePortAdmission.accepted_terminal D core P H ha
  unfold original OracleDecisionFeasibilityCore.original
  rw [RawCutProverCompiler.experiment_eval, RawCutProverCompiler.experiment_eval,
    admitted_verifier_eq D core H _ _ hg]

theorem admitted_recorded_eq (D : LiteralByteProtocol.Decoder) (core : Decision)
    (P : Prover) (H : Bytes → State)
    (ha : FS2.accepts (eval H (original D (admit core) P))) :
    eval H (recorded D (admit core) P) = eval H (recorded D core P) := by
  have hg := OraclePortAdmission.accepted_terminal D core P H ha
  have he := admitted_original_eq D core P H ha
  unfold original OracleDecisionFeasibilityCore.original at he
  unfold recorded OracleDecisionPrereqStarts.annotated
  rw [OracleDecisionFeasibilityCompiler.compiled_experiment_eval,
    OracleDecisionFeasibilityCompiler.compiled_experiment_eval, he]
  have hp : (eval H (experiment P (verifier D core))).2.1 = (eval H P).2 := by
    rw [RawCutProverCompiler.experiment_eval]
  dsimp only
  rw [congrArg Prod.fst hp, congrArg Prod.snd hp]
  rw [admitted_verifier_eq D core H _ _ hg]

/-- The conservative endpoint specialized to this kernel still displays
completion and checked acceptance. They are not inferred from its budget. -/
theorem final_soundness
    (D : LiteralByteProtocol.Decoder) (cs : List Commitment) (duplicates frames : List Bytes)
    (ha : Admissible cs duplicates frames) (P : Prover) (Q : Nat)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (hcompletion : OraclePortConsumer.Completion D (decision cs duplicates frames) P (Q + 1161))
    (hchecks : OraclePortConsumer.CheckedAcceptance D (decision cs duplicates frames) P (Q + 1161))
    (e : RawExtractorCostComposedBin.CostedExtractor)
    (p : RawExtractorCostComposedV2.Parameters)
    (hledger : RawExtractorCostComposedBin.LedgerRefinement e p (Q + 1161)) :
    lazyMean (recorded D (decision cs duplicates frames) P) emptyTable
      RawRecordedOracleExtractionMassBin.failureMass +
      QueryScanModelFailure.failureProbability (2^18) ≤ OraclePortHeadline.totalBound Q :=
  (OraclePortHeadline.final_soundness D (decision cs duplicates frames) P Q hqueries
    (budget cs duplicates frames ha) hcompletion hchecks e p hledger).2.2.2.1

#print axioms budget
#print axioms admitted_verifier_eq
#print axioms admitted_original_eq
#print axioms admitted_recorded_eq
#print axioms final_soundness
end AspisR1.OraclePortMultiKernel
end
