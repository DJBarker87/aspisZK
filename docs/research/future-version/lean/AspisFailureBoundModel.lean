import AspisFailureBoundJoined
import AspisNumericBound
import AspisRec40FinalDecoding

/-! The Aspis failure bound with its last open hypothesis discharged.

Kind of result: a MODEL THEOREM about the 40-row recorded experiment
(`AspisFailureBound.exp`). It is not a bound on the deployed program. It has no
account term, no payout conjunct and no campaign accounting.

`final_decoding40`: `AspisFailureBound.Joined.FinalDecoding40 D P Q` holds for
every decoder, prover and budget (`AspisRec40.FinalDecoding.final_decodes`:
the follow, W1 to W4, the literal late-row form from canonicalisation).
`failure_bound40P_model`: the conclusion of
`AspisFailureBound.Joined.failure_bound40P_of_final` with `hq` only.
`failure_le_per_query_model`: the per-query form
(`AspisNumeric.Bound.failure_le_per_query`) with `hQ` and `hq` only. -/
set_option autoImplicit false
noncomputable section
namespace AspisFailureBoundModel
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound AspisV8PairedCommitment
open AspisR1 OraclePortStoredExperimentC4 RawRecordedOracleExtractionMassBin
open AspisCharge40 AspisRowStarts40 AspisPerStep.RowStarts

theorem final_decoding40 (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (_hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    AspisFailureBound.Joined.FinalDecoding40 D P Q :=
  fun H hQ hout format tag hlate =>
    AspisRec40.FinalDecoding.final_decodes D P (Q+1111) H hQ hout format tag hlate

theorem failure_bound40P_model (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    lazyMean (AspisFailureBound.exp D P) emptyTable failureMass +
        QueryScanModelFailure.failureProbability (2^18) ≤
      BinCombinedMerkleCollision.kappa (Q+1111) +
        ((Q : ℚ) * capMax + verifierCharge40) + 1/(2:ℚ)^126 + 1/(2:ℚ)^454 :=
  AspisFailureBound.Joined.failure_bound40P_of_final D P Q hq (final_decoding40 D P Q hq)

theorem failure_le_per_query_model (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hQ : Q ≤ 2^150)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    lazyMean (AspisFailureBound.exp D P) emptyTable failureMass +
        QueryScanModelFailure.failureProbability (2^18) ≤
      ((Q : ℚ) + 1) / 2^100 :=
  AspisNumeric.Bound.failure_le_per_query D P Q hQ hq (final_decoding40 D P Q hq)

/-- Non-vacuity of `hq`: a prover that makes no oracle query and outputs any
statement and proof satisfies `hq` at every budget, so both model theorems
apply to it; any prover whose query count is bounded by `Q` in every oracle
world satisfies `hq` at `Q`. -/
theorem hq_of_done (x : Input) (Q : Nat) :
    ∀ H : Bytes → State, (eval H (Program.done x : Prover)).1.length ≤ Q :=
  fun _ => Nat.zero_le Q

#print axioms final_decoding40
#print axioms failure_bound40P_model
#print axioms failure_le_per_query_model
#print axioms hq_of_done

end AspisFailureBoundModel
end
