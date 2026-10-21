import OraclePortStoredDecisionDraftC4
import OraclePortDuplicateBindingDraft

/-! Shared-tree recovery on an explicitly containing trace, independent of
any fixed old decision/prover carrier. This is the selected-opening lemma
needed by the additional stored-proof experiment. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortStoredLeafRecoveryC4
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OracleDecisionMultiRecovery (OpenedAt)

theorem slots_accepted (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (ss : List (Nat × Nat)) (accepted : (eval H (verifySlots p q ss)).2 = true)
    (bk : Nat × Nat) (member : bk ∈ ss) :
    (eval H (verifySlot p q bk.1 bk.2)).2 = true := by
  induction ss with
  | nil => simp only [List.not_mem_nil] at member
  | cons head rest ih =>
    simp only [verifySlots,eval_bind,eval,Bool.and_eq_true] at accepted
    rcases List.mem_cons.mp member with same | member
    · subst bk; exact accepted.1
    · exact ih accepted.2 member

theorem slots_read (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (ss : List (Nat × Nat)) (bk : Nat × Nat) (member : bk ∈ ss)
    (a : Bytes) (read : Read (eval H (verifySlot p q bk.1 bk.2)).1 a) :
    Read (eval H (verifySlots p q ss)).1 a := by
  induction ss with
  | nil => simp only [List.not_mem_nil] at member
  | cons head rest ih =>
    simp only [Read,verifySlots,eval_bind,eval,List.append_nil,List.map_append,List.mem_append]
    rcases List.mem_cons.mp member with same | member
    · subst bk; exact Or.inl read
    · exact Or.inr (ih member)

theorem tree_inputs_read (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch kind : Nat) (a : Bytes)
    (ha : a ∈ OracleDecisionMultiRecovery.inputs H (tree p q batch kind)) :
    Read (eval H (verifySlot p q batch kind)).1 a := by
  have read : Read (eval H (execute (tree p q batch kind))).1 a := by
    rw [(execute_trace H _).1]
    simpa only [Read,OracleDecisionMultiRecovery.execute_inputs] using ha
  simp only [Read,verifySlot,eval_bind,eval,List.append_nil,List.map_append,List.mem_append]
  exact Or.inl read

/-- Every selected source position, including duplicates, has a path whose
leaf bytes equal its own opening on a collision-free containing trace. -/
theorem selected_path (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch kind pos : Nat) (member : pos ∈ batchPositions batch)
    (accepted : (eval H (verifySlot p q batch kind)).2 = true)
    (tr : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ tr, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (verifySlot p q batch kind)).1 a → Read tr a)
    (bound : firstReads emptyTable tr ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable tr) :
    ∃ path, path.length = 18 ∧ OpenedAt (tree p q batch kind) path (leaf p kind pos) := by
  obtain ⟨path,len,opened⟩ := OraclePortCoverageDraft.selected_opened p q batch kind pos member
  have same : leaf p kind pos = input p q batch kind (index q kind pos) := by
    by_cases representative : pos = position q batch kind (index q kind pos)
    · unfold input; rw [← representative]
    · have duplicate : pos ∈ duplicatePositions q batch kind :=
        List.mem_filter.mpr ⟨member,by simpa only [decide_eq_true_eq] using representative⟩
      exact OraclePortDuplicateBindingDraft.slot_duplicate_bytes H p q batch kind pos
        duplicate accepted tr Q consistent contains bound clean
  refine ⟨path,len,?_⟩
  rw [same]
  exact opened

/-- Recovery at the actual commitment cut, with no independent-path rehash.
The path is extracted symbolically from the tree already executed. -/
theorem selected_recovery (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
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
    ∃ path : List (Fin 2), path.length = 18 ∧
      BinMerkleLeafRecovery.recover
        (BinMerkleRecordedLog.nodes (BinRawByteCutRecovery.cut tr frame))
        (BinMerkleRecordedLog.leaves tag width (BinRawByteCutRecovery.cut tr frame))
        path.reverse (committedRoot p kind) = some (packed,salt) := by
  obtain ⟨path,len,opened⟩ := selected_path H p q batch kind pos member accepted
    tr Q consistent contains bound clean
  rw [leafBytes] at opened
  obtain ⟨authentication,root,reads⟩ := OracleDecisionMultiRecovery.shared_path H opened
  refine ⟨path,len,?_⟩
  apply BinRawByteCutRecovery.recover_at_first_commitment SelectedTranscriptParams.params.iv
    H tr Q consistent bound clean tag width packed salt packedWidth saltWidth
    authentication (committedRoot p kind) frame j frameRead rootRead
  · rw [BinMerkleProgram.eval_leafProgram]
    exact root.trans (slot_root H p q batch kind accepted)
  · intro a ha
    rw [BinMerkleProgram.eval_leafProgram] at ha
    change a ∈ ((BinMerkle32Leaf.fullTrace H authentication _).map (fun b => (b,H b))).map Prod.fst at ha
    simp only [List.map_map,Function.comp_def,List.map_id] at ha
    exact contains a (tree_inputs_read H p q batch kind a (reads a ha))

#print axioms slots_accepted
#print axioms slots_read
#print axioms tree_inputs_read
#print axioms selected_path
#print axioms selected_recovery
end AspisR1.OraclePortStoredLeafRecoveryC4
end
