import OraclePortCompletionDraft
import OraclePortHeadline

/-! Conditional draft endpoint with completion derived from checked syntax.
The typed acceptance premise remains; this is not the frozen dV endpoint. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortPrefixHeadlineDraft
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open OraclePortExperiment
open OraclePortAdmission (admit)
open RawCutProverCompiler (Prover RunView)
open RawExtractorCostComposedV2 (Parameters Coins)
open RawExtractorCostComposedBin
abbrev totalBound := OraclePortHeadline.totalBound
abbrev Qmax := OraclePortHeadline.Qmax

theorem completion
    (D : LiteralByteProtocol.Decoder) (core : Decision) (P : Prover) (Q : Nat)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (hbudget : Budget (admit core))
    (hchecks : OraclePortConsumer.CheckedAcceptance D (admit core) P (Q + 1161)) :
    OraclePortConsumer.Completion D (admit core) P (Q + 1161) := by
  apply OraclePortCompletionDraft.completion_of_checks D (admit core) P (Q+1161) _ hchecks
    (OraclePortAdmission.accepted_tag D core P)
  intro H
  have he : firstReads emptyTable (eval H (recorded D (admit core) P)).1 =
      firstReads emptyTable (eval H (original D (admit core) P)).1 :=
    OracleDecisionFeasibilityCompiler.firstReads_eq D (admit core)
      (BinCompiledRunWordStability.wordsFromRun D) P H
  rw [← he]
  exact OraclePortExperiment.first_reads D (admit core) hbudget P Q hqueries H

theorem final_soundness
    (D : LiteralByteProtocol.Decoder) (core : Decision) (P : Prover) (Q : Nat)
    (tape : R9PoolConcreteExperiment.Tape) (policy : R9PoolConcreteExperiment.Policy)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (hbudget : Budget (admit core))
    (hchecks : OraclePortConsumer.CheckedAcceptance D (admit core) P (Q + 1161))
    (e : CostedExtractor) (p : Parameters)
    (h_M10_ledger : LedgerRefinement e p (Q + 1161)) :
    (∀ H : Bytes → State, (eval H (recorded D (admit core) P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((e.eval (eval H (recorded D (admit core) P)) coins).2.total : ℚ)) ≤ (p.attemptBudget : ℚ)) ∧
    (∀ run coins w, (e.eval run coins).1 = some w → LiteralProtocol.relation run.2.1.1 w) ∧
    (1/(2:ℚ)^126 + 1/(2:ℚ)^454 ≤ 1/(2:ℚ)^120) ∧
    (R9DeployedBinaryExperiment.deployedFailureModel (OraclePortPool.tx1 D P tape)
      (OraclePortPool.poolTx2 D (admit core) P policy) ≤ totalBound Q) ∧
    (32 ≤ Q → Q ≤ Qmax →
      R9DeployedBinaryExperiment.deployedFailureModel (OraclePortPool.tx1 D P tape)
      (OraclePortPool.poolTx2 D (admit core) P policy) ≤ (Q+1:ℚ)*(1/(2:ℚ)^100)) := by
  exact OraclePortHeadline.final_soundness D (admit core) P Q tape policy hqueries hbudget
    (completion D core P Q hqueries hbudget hchecks) hchecks e p h_M10_ledger

#print axioms completion
#print axioms final_soundness
end AspisR1.OraclePortPrefixHeadlineDraft
end
