import OracleDecisionMultiRecovery

/-! Shared-path recovery in the actual annotation compiler's recorded log.
The repeated verifier does not need independent authentication paths. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionMultiCompiledRecovery
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OracleDecisionFeasibilityCore OracleDecisionMultiTree OracleDecisionMultiRecovery
open OracleDecisionPrereqStarts
open RawCutProverCompiler (Prover RunView)
open CanonicalCutEnrichedTranscript (Words)

theorem compiler_contains (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (H : Bytes → State) (words : RunView → Words) (P : Prover) (b : Bytes)
    (hb : Read (eval H (original D dO P)).1 b) :
    Read (eval H (annotated D dO words P)).1 b := by
  rw [original, RawCutProverCompiler.experiment_eval] at hb
  rw [annotated, OracleDecisionFeasibilityCompiler.compiled_experiment_eval,
    RawCutProverCompiler.experiment_eval]
  change b ∈ ((_ ++ _ ++ _).map Prod.fst)
  simp only [List.map_append, List.mem_append] at hb ⊢
  rcases hb with hp | hv
  · exact Or.inl (Or.inl hp)
  · exact Or.inl (Or.inr hv)

/-- Every leaf represented by an occupied position is recovered in the
compiled experiment, under that very experiment's collision exclusion. -/
theorem accepted_leaf_recovery (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (cs : List Commitment) (duplicates frames : List Bytes) (P : Prover) (words : RunView → Words)
    (c : Commitment) (hc : c ∈ cs) (slots : List (Fin 2))
    (tag : BinMerkle32Path.Byte) (width : Nat) (packed salt : Bytes)
    (ho : OpenedAt c.tree slots (BinMerkle32Leaf.leafInput tag packed salt))
    (hw : packed.length = width) (hs : salt.length = 32) (iv : State) (Q : Nat)
    (frame : Bytes) (j : Fin 5)
    (hframe : Read (eval H (annotated D (decision cs duplicates frames) words P)).1 frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some c.committed)
    (hQ : firstReads emptyTable (eval H (annotated D (decision cs duplicates frames) words P)).1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable (eval H (annotated D (decision cs duplicates frames) words P)).1)
    (hacc : (eval H (annotated D (decision cs duplicates frames) words P)).2.2 = true) :
    BinMerkleLeafRecovery.recover
      (BinMerkleRecordedLog.nodes (BinRawByteCutRecovery.cut
        (eval H (annotated D (decision cs duplicates frames) words P)).1 frame))
      (BinMerkleRecordedLog.leaves tag width (BinRawByteCutRecovery.cut
        (eval H (annotated D (decision cs duplicates frames) words P)).1 frame))
      slots.reverse c.committed = some (packed, salt) := by
  obtain ⟨path, hp, ht⟩ := shared_path H ho
  have horig : (eval H (original D (decision cs duplicates frames) P)).2.2 = true :=
    (OracleDecisionFeasibilityCompiler.public_and_acceptance D
      (decision cs duplicates frames) words P H).2.symm.trans hacc
  apply BinRawByteCutRecovery.recover_at_first_commitment iv H _ Q
    (FS.eval_consistent H _) hQ hout tag width packed salt hw hs path c.committed
    frame j hframe hpred
  · rw [BinMerkleProgram.eval_leafProgram]
    exact hp.trans (accepted_roots D H cs duplicates frames P horig c hc)
  · intro b hb
    rw [BinMerkleProgram.eval_leafProgram] at hb
    change b ∈ ((BinMerkle32Leaf.fullTrace H path _).map (fun a => (a,H a))).map Prod.fst at hb
    simp only [List.map_map, Function.comp_def] at hb
    change b ∈ List.map id (BinMerkle32Leaf.fullTrace H path _) at hb
    rw [List.map_id] at hb
    exact compiler_contains D _ H words P b
      (original_reads D H cs duplicates frames P c hc b (ht b hb))

#print axioms compiler_contains
#print axioms accepted_leaf_recovery
end AspisR1.OracleDecisionMultiCompiledRecovery
end
