import Port6AUTH_Prefix
import RawExtractorCostComposedBin
import ActualCostedExtractorM10
import ClosedAllocationLedgerM10
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6AUTH_Accounting
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortRuntimeBindingC7
open Port1_StoredCarrier Port6AUTH_Prefix
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget

/-- Physicality is proved for the existing Port1 driver. Thus the second pass
repeats the SAME verifier trace, even if its first pass rejected. All prefix
queries are retained and only repeated addresses stop costing first reads. -/
theorem first_reads (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver)
    (physical : Physical rust) (H : Bytes → State) :
    firstReads emptyTable (eval H (source D rust P)).1=
      firstReads emptyTable (eval H (originalWith rust (canon (lift P)))).1 := by
  have same (w : CanonicalCutEnrichedTranscript.Words) (i : Input) : rust (enrich w i)=rust i :=
    physical _ _ rfl rfl
  rw [source_eval,OraclePortFrozen2Join.annotatedWith_eval]
  dsimp only [view]
  rw [same,OraclePortFrozen2Join.originalWith_eval]
  exact OracleProgramRecording.firstReads_repeat_suffix _ _

theorem budget (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (physical : Physical rust)
    (calls : ∀ H i, (eval H (rust i)).1.length ≤ 1161) (H : Bytes → State) :
    firstReads emptyTable (eval H (source D rust P)).1 ≤ Q+1161 := by
  rw [first_reads D rust P physical H,OraclePortFrozen2Join.originalWith_eval]
  have h := VerifierCallBudget.firstReads_le_length emptyTable
    ((eval H (canon (lift P))).1 ++ (eval H (rust (eval H (canon (lift P))).2)).1)
  rw [List.length_append] at h
  have hp : (eval H (canon (lift P))).1.length ≤ Q := by
    simpa only [canon_eval,lift_eval] using hq H
  exact h.trans (Nat.add_le_add hp (calls H _))

/-- Total query cost retains both passes, not just distinct query addresses. -/
theorem log_length (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (calls : ∀ H i, (eval H (rust i)).1.length ≤ 1161) (H : Bytes → State) :
    (eval H (source D rust P)).1.length ≤ Q+2322 := by
  rw [source_eval,OraclePortFrozen2Join.annotatedWith_eval]
  dsimp only [view]
  rw [List.length_append,OraclePortFrozen2Join.originalWith_eval]
  simp only [List.length_append]
  have hp : (eval H (canon (lift P))).1.length ≤ Q := by
    simpa only [canon_eval,lift_eval] using hq H
  have h1 := calls H (eval H (canon (lift P))).2
  have h2 := calls H (enrich (build D (view (eval H (originalWith rust (canon (lift P))))))
    (eval H (originalWith rust (canon (lift P)))).2.1)
  simp only [OraclePortFrozen2Join.originalWith_eval,view] at h2
  omega

/-- Actual SOURCE-record extractor work, with the unchanged allocation ledger.
The accepted run here is not replaced by the frozen model run. -/
theorem extractor_cost (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (calls : ∀ H i, (eval H (rust i)).1.length ≤ 1161) (H : Bytes → State)
    (accepted : (eval H (source D rust P)).2.2=true) :
    mean (fun coins : RawExtractorCostComposedV2.Coins =>
      ((ActualCostedExtractorM10.extractor.eval (eval H (source D rust P)) coins).2.total : ℚ)) ≤
        ((CostedAllocationLedgerM10.params (Q+1161)).attemptBudget : ℚ) := by
  exact (RawExtractorCostComposedBin.accepted_attempt_cost
    ActualCostedExtractorM10.extractor (CostedAllocationLedgerM10.params (Q+1161))
    (Q+1161) (ClosedAllocationLedgerM10.ledger (Q+1161)) _ accepted
    (log_length D rust P Q hq calls H)).2

#print axioms first_reads
#print axioms budget
#print axioms log_length
#print axioms extractor_cost
end AspisR1.Port6AUTH_Accounting
end
