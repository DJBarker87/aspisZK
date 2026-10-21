import OraclePortRouteIndexC4
import OraclePortStoredLeafRecoveryC4

/-! Recover at the exact queried binary address. A path of the right length
alone would not identify the selected packed map used by the compiler. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortIndexedRecoveryC4
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OracleDecisionMultiRecovery (OpenedAt)

theorem indexed_route (p : Parsed) (q : Fin 22 → Fin 262144) (batch kind pos : Nat)
    (member : pos ∈ batchPositions batch) :
    OpenedAt (tree p q batch kind) (BinMultiproof.slots 18 (index q kind pos)).reverse
      (input p q batch kind (index q kind pos)) := by
  unfold tree
  have bound : index q kind pos < 2^18 := by
    unfold index
    dsimp only
    split
    · have b := (q ⟨pos%22,Nat.mod_lt _ (by decide)⟩).isLt
      omega
    · exact (q _).isLt
  simpa only [Nat.sub_zero] using OraclePortRouteIndexC4.opened_exact
    (selected q batch kind) (input p q batch kind) (sibling p q batch kind)
    18 0 (index q kind pos) (List.mem_map.mpr ⟨pos,member,rfl⟩) (Nat.zero_le _) bound

theorem own_indexed_route (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch kind pos : Nat) (member : pos ∈ batchPositions batch)
    (accepted : (eval H (verifySlot p q batch kind)).2 = true)
    (tr : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ tr, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (verifySlot p q batch kind)).1 a → Read tr a)
    (bound : firstReads emptyTable tr ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable tr) :
    OpenedAt (tree p q batch kind) (BinMultiproof.slots 18 (index q kind pos)).reverse
      (leaf p kind pos) := by
  have opened := indexed_route p q batch kind pos member
  have same : leaf p kind pos = input p q batch kind (index q kind pos) := by
    by_cases representative : pos = position q batch kind (index q kind pos)
    · unfold input; rw [← representative]
    · have duplicate : pos ∈ duplicatePositions q batch kind :=
        List.mem_filter.mpr ⟨member,by simpa only [decide_eq_true_eq] using representative⟩
      exact OraclePortDuplicateBindingDraft.slot_duplicate_bytes H p q batch kind pos
        duplicate accepted tr Q consistent contains bound clean
  rw [same]
  exact opened

theorem recovery_at_index (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch kind pos : Nat) (member : pos ∈ batchPositions batch)
    (accepted : (eval H (verifySlot p q batch kind)).2 = true)
    (tr : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ tr, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (verifySlot p q batch kind)).1 a → Read tr a)
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
  have opened := own_indexed_route H p q batch kind pos member accepted
    tr Q consistent contains bound clean
  rw [leafBytes] at opened
  have witness := OracleDecisionMultiRecovery.shared_path H opened
  obtain ⟨path,root,reads⟩ := witness
  apply BinRawByteCutRecovery.recover_at_first_commitment SelectedTranscriptParams.params.iv
    H tr Q consistent bound clean tag width packed salt packedWidth saltWidth
    path (committedRoot p kind) frame j frameRead rootRead
  · rw [BinMerkleProgram.eval_leafProgram]
    exact root.trans (slot_root H p q batch kind accepted)
  · intro a ha
    rw [BinMerkleProgram.eval_leafProgram] at ha
    change a ∈ ((BinMerkle32Leaf.fullTrace H path _).map (fun b => (b,H b))).map Prod.fst at ha
    simp only [List.map_map,Function.comp_def] at ha
    change a ∈ List.map id (BinMerkle32Leaf.fullTrace H path _) at ha
    rw [List.map_id] at ha
    exact contains a (OraclePortStoredLeafRecoveryC4.tree_inputs_read H p q batch kind a (reads a ha))

#print axioms indexed_route
#print axioms own_indexed_route
#print axioms recovery_at_index
end AspisR1.OraclePortIndexedRecoveryC4
end
