import AspisRec40CleanJoin

/-! Aspis: the protocol-level failure bound (form (P) of ASPIS-FAILURE-BOUND.md)
with two of the assembly's three hypotheses discharged.

`AspisFailureBound.failure_bound40P` takes `AcceptedChecks40`, `WordAlignment40`
and `HitInPrefix40` as hypotheses. `AspisRec40.CleanJoin` proves the first two
from the query hypothesis alone and the third from one statement about rows
33 to 39. This file only composes them, so that the bound is stated with the
single hypothesis that is still open.

Kind of result: a CONDITIONAL MODEL THEOREM. It is not a bound on the
deployed program. It has no account term and no payout conjunct. No figure
follows from it while `FinalDecoding40` is open.

`FinalDecoding40 D P Q` is that hypothesis, named: on the charged run of the
40-row experiment, under R1's four premises (first reads at most `Q + 1111`,
no collision event at `Q + 1111`, the wire format, statement tag 2) AND the
premise that rows 33 to 39 of the proof are payload messages
(`FinalShape.LatePayload`), the Aspis decoder recovers rows 33 to 39
(`CleanStatement.FinalDecodes`). It is a statement about the model only; it
is to be proved, not assumed.

Second form. The first form of this file (LDJ-01, LDJ-05) had no premise on
rows 33 to 39. That hypothesis is false for a prover that sends `.initial` at
a late row: `AspisRec40.FinalShape.finalDecodes_fails_initial` (found by the
soundness lead's reviewer; R1's four premises read only rows 0 to 32, the
statement and the trace). The theorem was therefore vacuous for such provers.
The added premise is not an assumption of the bound: inside
`AspisRec40.Clean.hit_in_prefix_of` it is derived from the acceptance checks
(`FinalShape.latePayload_of_checks`), and the hit-in-prefix step is only
used on accepted runs. That an honest run meets all five premises is argued
in RECORDED-EXPERIMENT-40.md section 11.4, not compiled. -/
set_option autoImplicit false
noncomputable section
namespace AspisFailureBound.Joined
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound AspisV8PairedCommitment
open AspisR1 OraclePortStoredExperimentC4 RawRecordedOracleExtractionMassBin
open AspisCharge40 AspisRowStarts40 AspisPerStep.RowStarts

/-- The one hypothesis still open: decoding of rows 33 to 39 on the charged
run. Its body is the premise of `AspisRec40.CleanJoin.hit_in_prefix40`. -/
def FinalDecoding40 (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat) : Prop :=
  ∀ H : Bytes → State,
    firstReads emptyTable (eval H (AspisRec40.ChargePrefix.base D P)).1 ≤ Q+1111 →
    ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
        BinRawByteCollisionTargets.pred (Q+1111)) emptyTable
        (eval H (AspisRec40.ChargePrefix.base D P)).1 →
    RWireCheckedFormat.Format (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 →
    (eval H (AspisRec40.ChargePrefix.base D P)).2.1.1.tag = 2 →
    AspisRec40.FinalShape.LatePayload (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 →
    AspisRec40.CleanStatement.FinalDecodes D H (eval H (AspisRec40.ChargePrefix.charged D P))

/-- Form (P) with one open hypothesis. -/
theorem failure_bound40P_of_final (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (hfinal : FinalDecoding40 D P Q) :
    lazyMean (AspisFailureBound.exp D P) emptyTable failureMass +
        QueryScanModelFailure.failureProbability (2^18) ≤
      BinCombinedMerkleCollision.kappa (Q+1111) +
        ((Q : ℚ) * capMax + verifierCharge40) + 1/(2:ℚ)^126 + 1/(2:ℚ)^454 :=
  AspisFailureBound.failure_bound40P D P Q hq
    (AspisRec40.CleanJoin.accepted_checks40 D P Q hq)
    (AspisRec40.CleanJoin.word_alignment40 D P Q hq)
    (AspisRec40.CleanJoin.hit_in_prefix40 D P Q hq hfinal)

#print axioms failure_bound40P_of_final
end AspisFailureBound.Joined
end
