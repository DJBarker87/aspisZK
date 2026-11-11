import AspisFailureBoundJoined
import AspisNumeric

/-! The per-query form of the Aspis failure bound, linked to the bound
theorem by Lean.

Kind of result: a CONDITIONAL MODEL THEOREM. It composes
`AspisFailureBound.Joined.failure_bound40P_of_final` with the arithmetic of
`AspisNumeric.rhs_per_query`. It is conditional on `FinalDecoding40`, which is
open; it has no account term, no payout conjunct and no campaign accounting;
it says nothing about the deployed program. -/
set_option autoImplicit false
noncomputable section
namespace AspisNumeric.Bound
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound AspisV8PairedCommitment
open AspisR1 OraclePortStoredExperimentC4 RawRecordedOracleExtractionMassBin
open AspisCharge40 AspisRowStarts40 AspisPerStep.RowStarts

/-- Form (P) per query: for `Q ≤ 2^150`, under `FinalDecoding40`, the failure
mass plus the query-scan failure is at most `(Q + 1) / 2^100`. -/
theorem failure_le_per_query (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hQ : Q ≤ 2^150)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (hfinal : AspisFailureBound.Joined.FinalDecoding40 D P Q) :
    lazyMean (AspisFailureBound.exp D P) emptyTable failureMass +
        QueryScanModelFailure.failureProbability (2^18) ≤
      ((Q : ℚ) + 1) / 2^100 :=
  le_trans (AspisFailureBound.Joined.failure_bound40P_of_final D P Q hq hfinal)
    (AspisNumeric.rhs_per_query Q hQ)

#print axioms failure_le_per_query
end AspisNumeric.Bound
end
