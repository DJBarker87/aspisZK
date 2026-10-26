import F3T_Probability
import F3T_Cost
import StartChargeNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_ModelClaims
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open FS FS2
open F3T_Experiment F3T_Charged F3T_Canon
open RawRecordedOracleExtractionMassBin RawExtractorCostComposedV2

def failure (D : LiteralByteProtocol.Decoder) (P : Prover) : Rat :=
  lazyMean (projected D (canon P)) emptyTable failureMass + QueryScanModelFailure.failureProbability (2^18)

theorem failure_bound (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State,(eval H P).1.length≤Q) :
    failure D P ≤ StartChargeNumeric.totalBound Q := by
  apply (add_le_add (F3T_Probability.failure_bound D P Q hq)
    QueryScanModelFailure.exhaustion_bound).trans_eq
  unfold StartChargeNumeric.totalBound OracleDecisionPrereqNumeric.envelope
  ring

theorem per_attempt (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State,(eval H P).1.length≤Q)
    (range : Q ≤ OraclePortHeadlineFrozen2.Qmax) :
    failure D P ≤ (Q+1:Rat)*(1/(2:Rat)^100) :=
  (failure_bound D P Q hq).trans (StartChargeNumeric.safe_range Q range)

theorem zero_queries (D : LiteralByteProtocol.Decoder) (P : Prover)
    (hq : ∀ H : Bytes → State,(eval H P).1.length≤0) :
    failure D P ≤ 1/(2:Rat)^100 :=
  (failure_bound D P 0 hq).trans StartChargeNumeric.zero_queries

#print axioms failure_bound
#print axioms per_attempt
#print axioms zero_queries
end AspisR1.F3T_ModelClaims
end
