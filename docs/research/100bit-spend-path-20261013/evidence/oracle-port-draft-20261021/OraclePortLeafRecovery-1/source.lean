import OraclePortMultiKernel

/-! Selected shared leaves are authenticated in the guarded compiler log.
The parser must still supply OpenedAt, widths, salts and root-frame linkage. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortLeafRecovery
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open RawCutProverCompiler (Prover)
open OraclePortExperiment (recorded)
open OraclePortMultiKernel (decision)
open OracleDecisionMultiTree (Commitment)
open OracleDecisionMultiRecovery (OpenedAt)

theorem accepted_leaf_recovery (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (cs : List Commitment) (duplicates frames : List Bytes) (P : Prover)
    (c : Commitment) (hc : c ∈ cs) (slots : List (Fin 2))
    (tag : BinMerkle32Path.Byte) (width : Nat) (packed salt : Bytes)
    (ho : OpenedAt c.tree slots (BinMerkle32Leaf.leafInput tag packed salt))
    (hw : packed.length = width) (hs : salt.length = 32) (iv : State) (Q : Nat)
    (frame : Bytes) (j : Fin 5)
    (hframe : Read (eval H (recorded D (decision cs duplicates frames) P)).1 frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some c.committed)
    (hQ : firstReads emptyTable (eval H (recorded D (decision cs duplicates frames) P)).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable (eval H (recorded D (decision cs duplicates frames) P)).1)
    (hacc : (eval H (recorded D (decision cs duplicates frames) P)).2.2 = true) :
    BinMerkleLeafRecovery.recover
      (BinMerkleRecordedLog.nodes (BinRawByteCutRecovery.cut
        (eval H (recorded D (decision cs duplicates frames) P)).1 frame))
      (BinMerkleRecordedLog.leaves tag width (BinRawByteCutRecovery.cut
        (eval H (recorded D (decision cs duplicates frames) P)).1 frame))
      slots.reverse c.committed = some (packed, salt) := by
  have ha : FS2.accepts (eval H (OraclePortExperiment.original D
      (decision cs duplicates frames) P)) :=
    (OracleDecisionFeasibilityCompiler.public_and_acceptance D (decision cs duplicates frames)
      (BinCompiledRunWordStability.wordsFromRun D) P H).2.symm.trans hacc
  have he := OraclePortMultiKernel.admitted_recorded_eq D
    (OracleDecisionMultiTree.decision cs duplicates frames) P H ha
  change eval H (recorded D (decision cs duplicates frames) P) =
    eval H (OracleDecisionPrereqStarts.annotated D
      (OracleDecisionMultiTree.decision cs duplicates frames)
      (BinCompiledRunWordStability.wordsFromRun D) P) at he
  rw [he] at hframe hQ hout hacc ⊢
  exact OracleDecisionMultiCompiledRecovery.accepted_leaf_recovery D H cs duplicates frames P
    (BinCompiledRunWordStability.wordsFromRun D) c hc slots tag width packed salt ho hw hs iv Q
    frame j hframe hpred hQ hout hacc

#print axioms accepted_leaf_recovery
end AspisR1.OraclePortLeafRecovery
end
