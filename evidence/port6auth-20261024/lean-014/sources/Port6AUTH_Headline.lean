import Port6AUTH_Probability
import Port1_CanonicalHeadline
import OraclePortHeadlineFrozen2PerAttempt
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6AUTH_Headline
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortRuntimeBindingC7
open Port1_StoredCarrier RawRecordedOracleExtractionMassBin Port6AUTH_Prefix
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget

theorem final_soundness (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (contains : ∀ H a, Read (eval H (Frozen2StartChargePrefix.charged D (lift P))).1 a →
      Read (eval H (source D rust P)).1 a)
    (budget : ∀ H, firstReads emptyTable (eval H (source D rust P)).1 ≤ Q+1161)
    (checks : CleanAcceptedModel D (source D rust P) (bad D P Q))
    (runtime : Runtime) (binding : StoredCarrierBinding D rust (lift P) runtime) :
    OraclePortHeadlineFrozen2PerAttempt.Claims D (lift P) Q runtime := by
  have queries := Port1_CanonicalHeadline.lift_queries P Q hq
  have hb := Port6AUTH_Probability.failure_bound D rust P Q hq contains budget checks
  have hr := Port6AUTH_Probability.runtime_transport D rust P runtime binding
  have ht : OraclePortHeadlineFrozen2PerAttempt.failureModel runtime ≤ StartChargeNumeric.totalBound Q := by
    apply (add_le_add (hr.trans hb) QueryScanModelFailure.exhaustion_bound).trans_eq
    unfold OraclePortHeadlineFrozen2PerAttempt.failureModel OraclePortHeadlineFrozen2.failureModel
      StartChargeNumeric.totalBound OracleDecisionPrereqNumeric.envelope
    ring
  refine ⟨?_,?_,R1FinalSoundnessNumeric.extractor_abort_allowance,ht,?_⟩
  · intro H ha
    change (eval H (OraclePortFrozen2Consumer.projected D (lift P))).2.2=true at ha
    exact (RawExtractorCostComposedBin.accepted_attempt_cost
      ActualCostedExtractorM10.extractor (CostedAllocationLedgerM10.params (Q+1161))
      (Q+1161) (ClosedAllocationLedgerM10.ledger (Q+1161)) _ ha
      (OraclePortFrozen2Probability.log_length D (lift P) Q queries H)).2
  · intro run coins w hw
    exact RawRecordedPublicSpendExtractorBin.returned_relation run coins w
      ((ActualCostedExtractorM10.extractor.value run coins).symm.trans hw)
  · intro hi
    exact ht.trans (StartChargeNumeric.safe_range Q hi)

/-- Whole repeated/adaptive experiment bound; all original additive terms. -/
theorem failure_bound (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (contains : ∀ H a, Read (eval H (Frozen2StartChargePrefix.charged D (lift P))).1 a →
      Read (eval H (source D rust P)).1 a)
    (budget : ∀ H, firstReads emptyTable (eval H (source D rust P)).1 ≤ Q+1161)
    (checks : CleanAcceptedModel D (source D rust P) (bad D P Q))
    (runtime : Runtime) (binding : StoredCarrierBinding D rust (lift P) runtime) :
    OraclePortHeadlineFrozen2PerAttempt.failureModel runtime ≤
      ((Q+34 : Nat) : ℚ)*PerAttemptEnvelope.B + BinCombinedMerkleCollision.kappa (Q+1161) +
        1/(2:ℚ)^126 + 1/(2:ℚ)^454 :=
  (final_soundness D rust P Q hq contains budget checks runtime binding).2.2.2.1

theorem zero_queries (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ 0)
    (contains : ∀ H a, Read (eval H (Frozen2StartChargePrefix.charged D (lift P))).1 a →
      Read (eval H (source D rust P)).1 a)
    (budget : ∀ H, firstReads emptyTable (eval H (source D rust P)).1 ≤ 0+1161)
    (checks : CleanAcceptedModel D (source D rust P) (bad D P 0))
    (runtime : Runtime) (binding : StoredCarrierBinding D rust (lift P) runtime) :
    OraclePortHeadlineFrozen2PerAttempt.failureModel runtime ≤ 1/(2:ℚ)^100 :=
  ((final_soundness D rust P 0 hq contains budget checks runtime binding).2.2.2.1).trans
    StartChargeNumeric.zero_queries

#print axioms final_soundness
#print axioms failure_bound
#print axioms zero_queries
end AspisR1.Port6AUTH_Headline
end
