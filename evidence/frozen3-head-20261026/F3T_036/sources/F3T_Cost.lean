import F3T_Accounting
import OraclePortFrozen2Headline
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Cost
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open F3T_Experiment F3T_Charged F3T_Canon
open RawExtractorCostComposedV2 (Coins)

theorem accepted_attempt_cost (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State,(eval H P).1.length≤Q) (H : Bytes → State)
    (accepted : (eval H (projected D (canon P))).2.2=true) :
    mean (fun coins : Coins=>
      ((ActualCostedExtractorM10.extractor.eval (eval H (projected D (canon P))) coins).2.total : Rat))≤
      ((CostedAllocationLedgerM10.params (Q+1161)).attemptBudget : Rat) := by
  exact (RawExtractorCostComposedBin.accepted_attempt_cost
    ActualCostedExtractorM10.extractor (CostedAllocationLedgerM10.params (Q+1161))
    (Q+1161) (ClosedAllocationLedgerM10.ledger (Q+1161)) _ accepted
    (F3T_Accounting.log_length D P Q hq H)).2

theorem returned_relation (run : RawCutProverCompiler.RunView) (coins : Coins)
    (w : LiteralProtocol.Witness)
    (returned : (ActualCostedExtractorM10.extractor.eval run coins).1=some w) :
    LiteralProtocol.relation run.2.1.1 w := by
  exact RawRecordedPublicSpendExtractorBin.returned_relation run coins w
    ((ActualCostedExtractorM10.extractor.value run coins).symm.trans returned)

#print axioms accepted_attempt_cost
#print axioms returned_relation
end AspisR1.F3T_Cost
end
