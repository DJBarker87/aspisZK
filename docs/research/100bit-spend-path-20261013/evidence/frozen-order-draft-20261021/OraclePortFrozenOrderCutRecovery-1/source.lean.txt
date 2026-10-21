import OraclePortFrozenOrderSlotPath

/-! Recover at the exact queried binary address. A path of the right length
alone would not identify the selected packed map used by the compiler. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortFrozenOrder
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OracleDecisionMultiRecovery (OpenedAt)

theorem recovery_at_index (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch kind pos : Nat) (member : pos ∈ batchPositions batch)
    (accepted : (eval H (verifySlot_frozen p q batch kind)).2 = true)
    (tr : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ tr, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (verifySlot_frozen p q batch kind)).1 a → Read tr a)
    (bound : firstReads emptyTable tr ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable tr)
    (frame : Bytes) (j : Fin 5) (frameRead : Read tr frame)
    (rootRead : BinRawByteCollisionTargets.pred j frame = some (committedRoot p kind))
    (tag : BinMerkle32Path.Byte) (width : Nat) (packed salt : Bytes)
    (leafBytes : leaf p kind pos = BinMerkle32Leaf.leafInput tag packed salt)
    (packedWidth : packed.length = width) (saltWidth : salt.length = 32) :
    BinRawByteCutStability.recoverAt tag width (BinRawByteCutRecovery.cut tr frame)
      (BinMultiproof.slots 18 (index q kind pos)) (committedRoot p kind) = some (packed,salt) := by
  obtain ⟨path,root,reads⟩ := slot_path H p q batch kind pos member accepted
  rw [leafBytes] at root reads
  apply BinRawByteCutRecovery.recover_at_first_commitment SelectedTranscriptParams.params.iv
    H tr Q consistent bound clean tag width packed salt packedWidth saltWidth
    path (committedRoot p kind) frame j frameRead rootRead
  · rw [BinMerkleProgram.eval_leafProgram]
    exact root
  · intro a ha
    rw [BinMerkleProgram.eval_leafProgram] at ha
    change a ∈ ((BinMerkle32Leaf.fullTrace H path _).map (fun b => (b,H b))).map Prod.fst at ha
    simp only [List.map_map,Function.comp_def] at ha
    change a ∈ List.map id (BinMerkle32Leaf.fullTrace H path _) at ha
    rw [List.map_id] at ha
    exact contains a (reads a ha)

#print axioms recovery_at_index
end AspisR1.OraclePortFrozenOrder
end
