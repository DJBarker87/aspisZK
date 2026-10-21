import OraclePortConsumer
import OraclePortPool
import OracleDecisionMultiNumeric
import RawRecordedActualAdaptiveFailureBoundBin
import RawExtractorCostComposedBin

/-! Draft generic composition. CleanModel is an explicit remaining model
obligation, not a renamed claim that R3/R13--R16 have been discharged. The
subject is a logical recorded experiment; source and Pool transport are separate. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortHeadline
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open OraclePortExperiment
open RawCutProverCompiler (Prover RunView)
open RawRecordedOracleExtractionMassBin
open RawExtractorCostComposedV2 (Parameters Coins)
open RawExtractorCostComposedBin

abbrev totalBound (Q : Nat) := OracleDecisionPrereqNumeric.envelope Q 1080 1161
abbrev Qmax := OracleDecisionMultiNumeric.safeMax
abbrev collision := RecordedBinaryExperimentBin.binaryCollision
abbrev dec := RecordedBinaryExperimentBin.dec

def bad (Q : Nat) (run : RunView) : Prop := collision (Q + 1161) run ∨
  hitsChain3 dec RawAdaptiveClassifierHitDensity.classifier emptyTable run.1

/-- Exactly the extractor's existing clean-model interface, on the new program. -/
abbrev CleanModel (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover)
    (Q : Nat) : Prop := CleanAcceptedModel D (recorded D dO P) (bad Q)

/-- The conservative start coefficient and five-reader collision allowance
are charged once on the same generalized annotated experiment. -/
theorem recorded_failure_bound
    (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover) (Q : Nat)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (hbudget : Budget dO) (hclean : CleanModel D dO P Q) :
    lazyMean (recorded D dO P) emptyTable failureMass ≤
      BinCombinedMerkleCollision.kappa (Q + 1161) +
      ((Q + 1080 : Nat) : ℚ) * PerAttemptEnvelope.B + 1/(2:ℚ)^126 := by
  let exp := recorded D dO P
  have hc := BinCombinedMerkleCollision.mass SelectedTranscriptParams.params.iv
    (Q + 1161) exp (first_reads D dO hbudget P Q hqueries)
  have hs := RawAdaptiveClassifierStartBound.shared_hit_mass_le_starts
    RawFullPublicSelection.select LiteralTableWordChoiceBin.choose exp (Q + 1080)
    (starts D dO hbudget P Q hqueries)
  apply shared_oracle_failure_le_supplied_hit_bound D exp (bad Q) hclean
  calc
    lazyMean exp emptyTable (fun run => indicator (bad Q run)) ≤
        lazyMean exp emptyTable (fun run => indicator (collision (Q + 1161) run) +
          indicator (hitsChain3 dec RawAdaptiveClassifierHitDensity.classifier emptyTable run.1)) :=
      AllAddressFiatShamir.lazyMean_mono_of_eval exp _ _ (fun _ => indicator_or_le _ _)
    _ = lazyMean exp emptyTable (fun run => indicator (collision (Q + 1161) run)) +
        lazyMean exp emptyTable (fun run =>
          indicator (hitsChain3 dec RawAdaptiveClassifierHitDensity.classifier emptyTable run.1)) :=
      lazyMean_add _ _ _ _
    _ ≤ _ := add_le_add hc hs

/-- Conditional draft endpoint. The shifted ledger is necessary on Q+2322;
no adequacy on that larger domain is inferred from the old ledger premise. -/
theorem final_soundness_of_clean
    (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover) (Q : Nat)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (hbudget : Budget dO) (hclean : CleanModel D dO P Q)
    (e : CostedExtractor) (p : Parameters)
    (h_M10_ledger : LedgerRefinement e p (Q + 1161)) :
    (∀ H : Bytes → State, (eval H (recorded D dO P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((e.eval (eval H (recorded D dO P)) coins).2.total : ℚ)) ≤ (p.attemptBudget : ℚ)) ∧
    (∀ run coins w, (e.eval run coins).1 = some w → LiteralProtocol.relation run.2.1.1 w) ∧
    (1/(2:ℚ)^126 + 1/(2:ℚ)^454 ≤ 1/(2:ℚ)^120) ∧
    (lazyMean (recorded D dO P) emptyTable failureMass +
      QueryScanModelFailure.failureProbability (2^18) ≤ totalBound Q) ∧
    (32 ≤ Q → Q ≤ Qmax →
      lazyMean (recorded D dO P) emptyTable failureMass +
        QueryScanModelFailure.failureProbability (2^18) ≤ (Q+1:ℚ)*(1/(2:ℚ)^100)) := by
  have hb := recorded_failure_bound D dO P Q hqueries hbudget hclean
  have ht : lazyMean (recorded D dO P) emptyTable failureMass +
      QueryScanModelFailure.failureProbability (2^18) ≤ totalBound Q := by
    apply (add_le_add hb QueryScanModelFailure.exhaustion_bound).trans_eq
    unfold totalBound OracleDecisionPrereqNumeric.envelope
    ring
  refine ⟨?_, ?_, R1FinalSoundnessNumeric.extractor_abort_allowance, ht, ?_⟩
  · intro H ha
    exact (accepted_attempt_cost e p (Q + 1161) h_M10_ledger _ ha
      (log_length D dO hbudget P Q hqueries H)).2
  · intro run coins w hw
    exact RawRecordedPublicSpendExtractorBin.returned_relation run coins w
      ((e.value run coins).symm.trans hw)
  · intro hlo hhi
    exact ht.trans (OracleDecisionMultiNumeric.safe_range Q hlo hhi)

/-- The model frontier is completion plus actual reader Checks, rather than
an opaque clean-model hypothesis. Neither frontier is called a source join. -/
theorem recorded_soundness
    (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover) (Q : Nat)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (hbudget : Budget dO)
    (hcompletion : OraclePortConsumer.Completion D dO P (Q + 1161))
    (hchecks : OraclePortConsumer.CheckedAcceptance D dO P (Q + 1161))
    (e : CostedExtractor) (p : Parameters)
    (h_M10_ledger : LedgerRefinement e p (Q + 1161)) :
    (∀ H : Bytes → State, (eval H (recorded D dO P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((e.eval (eval H (recorded D dO P)) coins).2.total : ℚ)) ≤ (p.attemptBudget : ℚ)) ∧
    (∀ run coins w, (e.eval run coins).1 = some w → LiteralProtocol.relation run.2.1.1 w) ∧
    (1/(2:ℚ)^126 + 1/(2:ℚ)^454 ≤ 1/(2:ℚ)^120) ∧
    (lazyMean (recorded D dO P) emptyTable failureMass +
      QueryScanModelFailure.failureProbability (2^18) ≤ totalBound Q) ∧
    (32 ≤ Q → Q ≤ Qmax →
      lazyMean (recorded D dO P) emptyTable failureMass +
        QueryScanModelFailure.failureProbability (2^18) ≤ (Q+1:ℚ)*(1/(2:ℚ)^100)) := by
  exact final_soundness_of_clean D dO P Q hqueries hbudget
    (OraclePortConsumer.clean_of_checks D dO P Q hqueries hbudget hcompletion hchecks)
    e p h_M10_ledger

/-- Draft headline at the constructed logical Pool instance. The two model
frontiers below remain additional to Rust equality and runtime assumptions. -/
theorem final_soundness
    (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover) (Q : Nat)
    (tape : R9PoolConcreteExperiment.Tape) (policy : R9PoolConcreteExperiment.Policy)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (hbudget : Budget dO)
    (hcompletion : OraclePortConsumer.Completion D dO P (Q + 1161))
    (hchecks : OraclePortConsumer.CheckedAcceptance D dO P (Q + 1161))
    (e : CostedExtractor) (p : Parameters)
    (h_M10_ledger : LedgerRefinement e p (Q + 1161)) :
    (∀ H : Bytes → State, (eval H (recorded D dO P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((e.eval (eval H (recorded D dO P)) coins).2.total : ℚ)) ≤ (p.attemptBudget : ℚ)) ∧
    (∀ run coins w, (e.eval run coins).1 = some w → LiteralProtocol.relation run.2.1.1 w) ∧
    (1/(2:ℚ)^126 + 1/(2:ℚ)^454 ≤ 1/(2:ℚ)^120) ∧
    (R9DeployedBinaryExperiment.deployedFailureModel (OraclePortPool.tx1 D P tape)
      (OraclePortPool.poolTx2 D dO P policy) ≤ totalBound Q) ∧
    (32 ≤ Q → Q ≤ Qmax →
      R9DeployedBinaryExperiment.deployedFailureModel (OraclePortPool.tx1 D P tape)
      (OraclePortPool.poolTx2 D dO P policy) ≤ (Q+1:ℚ)*(1/(2:ℚ)^100)) := by
  obtain ⟨hcost, hreturned, habort, hbound, _⟩ :=
    recorded_soundness D dO P Q hqueries hbudget hcompletion hchecks e p h_M10_ledger
  have ht := (OraclePortPool.deployed_transport D dO P tape policy).trans hbound
  exact ⟨hcost, hreturned, habort, ht,
    fun hlo hhi => ht.trans (OracleDecisionMultiNumeric.safe_range Q hlo hhi)⟩

#print axioms recorded_soundness
#print axioms final_soundness_of_clean
#print axioms recorded_failure_bound
#print axioms final_soundness
end AspisR1.OraclePortHeadline
end
