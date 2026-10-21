import OraclePortMultiKernel

/-! Full conditional headline specialized to the admitted multiproof kernel.
This is not a frozen dV: forest/frame parsing and typed binding remain open. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortMultiHeadline
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open OraclePortExperiment
open OraclePortHeadline (totalBound Qmax)
open RawCutProverCompiler (Prover)
open RawRecordedOracleExtractionMassBin
open RawExtractorCostComposedV2 (Parameters Coins)
open RawExtractorCostComposedBin

theorem final_soundness
    (D : LiteralByteProtocol.Decoder)
    (cs : List OracleDecisionMultiTree.Commitment) (duplicates frames : List Bytes)
    (ha : OracleDecisionMultiTree.Admissible cs duplicates frames)
    (P : Prover) (Q : Nat)
    (tape : R9PoolConcreteExperiment.Tape) (policy : R9PoolConcreteExperiment.Policy)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (hcompletion : OraclePortConsumer.Completion D (OraclePortMultiKernel.decision cs duplicates frames) P (Q + 1161))
    (hchecks : OraclePortConsumer.CheckedAcceptance D (OraclePortMultiKernel.decision cs duplicates frames) P (Q + 1161))
    (e : CostedExtractor) (p : Parameters)
    (h_M10_ledger : LedgerRefinement e p (Q + 1161)) :
    (∀ H : Bytes → State, (eval H (recorded D (OraclePortMultiKernel.decision cs duplicates frames) P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((e.eval (eval H (recorded D (OraclePortMultiKernel.decision cs duplicates frames) P)) coins).2.total : ℚ)) ≤ (p.attemptBudget : ℚ)) ∧
    (∀ run coins w, (e.eval run coins).1 = some w → LiteralProtocol.relation run.2.1.1 w) ∧
    (1/(2:ℚ)^126 + 1/(2:ℚ)^454 ≤ 1/(2:ℚ)^120) ∧
    (R9DeployedBinaryExperiment.deployedFailureModel (OraclePortPool.tx1 D P tape)
      (OraclePortPool.poolTx2 D (OraclePortMultiKernel.decision cs duplicates frames) P policy) ≤ totalBound Q) ∧
    (32 ≤ Q → Q ≤ Qmax →
      R9DeployedBinaryExperiment.deployedFailureModel (OraclePortPool.tx1 D P tape)
      (OraclePortPool.poolTx2 D (OraclePortMultiKernel.decision cs duplicates frames) P policy) ≤ (Q+1:ℚ)*(1/(2:ℚ)^100)) := by
  exact OraclePortHeadline.final_soundness D (OraclePortMultiKernel.decision cs duplicates frames)
    P Q tape policy hqueries (OraclePortMultiKernel.budget cs duplicates frames ha)
    hcompletion hchecks e p h_M10_ledger

#print axioms final_soundness
end AspisR1.OraclePortMultiHeadline
end
