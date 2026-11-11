import OraclePortFrozenOrderSlotPath
import AspisOneTxSummedLayout

/-! The Aspis one-transaction verifier: one merged in-place multiproof per tree
(item M2 of ONE-TRANSACTION-GAME.md), as R1's frozen-order slot program with
its four constants made parameters.

Kind of result: MODEL DEFINITIONS AND THEOREMS in R1's binary commitment model.
`slotB n cap start ps` is R1's `verifySlot_frozen` with the position list
`ps`, the well-formedness length bound `n`, the slot capacity `cap` and the
slot start `start` as parameters; `hashLeaves`, `runLevels` and `nodeCount`
are R1's, unchanged. `r1_slot_instance` proves by `rfl` that R1's slot program
is the instance `n = 16`, `cap = capacity (3*batch+kind)`, `start = slotStart
(3*batch+kind)`, `ps = sortedPositions q batch kind`; R1's `slot_path` and
`recovery_at_index` are re-derived from the generic theorems as checks.
The Aspis merged slot is the instance `n = 22`, `cap = mergedCapacity kind`,
`start = mergedStart kind`, `ps` = all 22 positions sorted by R1's key.

NOT established here: that `multiproof::verify_counting_merged`,
`merkle_verdict` and `merged_tree` (fused.rs:776-806) compute `verifyMerged`
(source refinement), in particular the 22-leaf bound of `MAX_MERGED`. -/
set_option autoImplicit false
noncomputable section
namespace AspisOneTx
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisR1 AspisR1.OracleDecisionMultiTree AspisR1.BinMerkle32Path
open AspisR1.OraclePortCompactDraft AspisR1.OraclePortSelectedDraft AspisR1.OraclePortBatchDraft
open AspisR1.OraclePortFrozenOrder
attribute [local instance] Classical.propDecidable

/-- R1's `wellFormed` with the length bound `16` as a parameter. -/
def wellFormedB (n : Nat) (is : List Nat) : Prop :=
  is ≠ [] ∧ is.length ≤ n ∧ is.Pairwise (· < ·) ∧ ∀ i ∈ is, i < 262144

/-- R1's `verifyInPlace` over `wellFormedB n`. -/
def verifyInPlaceB (n : Nat) (root : State) (live : Live) (nodes : Bytes) :
    Program Bytes State Bool :=
  if wellFormedB n (live.map Prod.fst) ∧ nodes.length % 32 = 0 then
    bind (runLevels 18 live nodes) fun out => .done (match out with
      | some ([(i,d)],remaining) => decide (i = 0 ∧ d = root ∧ remaining = [])
      | _ => false)
  else .done false

/-- R1's `slotTail` with the capacity and the slot start as parameters. -/
def tailB (n cap start : Nat) (p : Parsed) (kind : Nat) (live : Live) :
    Program Bytes State Bool :=
  let is := live.map Prod.fst
  if wellFormedB n is then
    let count := nodeCount 18 is
    let nodes := slice p.wire start (32*cap)
    if count ≤ cap ∧ nodes.length = 32*cap ∧
        nodes.drop (32*count) = List.replicate (32*(cap-count)) 0 then
      verifyInPlaceB n (committedRoot p kind) live (nodes.take (32*count))
    else .done false
  else .done false

/-- R1's `verifySlot_frozen` with the sorted position list as a parameter. -/
def slotB (n cap start : Nat) (ps : List Nat) (p : Parsed) (q : Fin 22 → Fin 262144)
    (kind : Nat) : Program Bytes State Bool :=
  bind (hashLeaves p q kind ps []) fun out =>
    match out with
    | none => .done false
    | some live => tailB n cap start p kind live

/-- R1's slot program is an instance (definitional). -/
theorem r1_slot_instance (p : Parsed) (q : Fin 22 → Fin 262144) (batch kind : Nat) :
    verifySlot_frozen p q batch kind =
      slotB 16 (capacity (3*batch+kind)) (slotStart (3*batch+kind))
        (sortedPositions q batch kind) p q kind := rfl

/-- All 22 positions, in R1's key order (index, then position): the order of
`merged_keys` (fused.rs:754-770). -/
def sortedAll (q : Fin 22 → Fin 262144) (kind : Nat) : List Nat :=
  (List.range 22).mergeSort (fun a b => decide
    (index q kind a < index q kind b ∨ index q kind a = index q kind b ∧ a ≤ b))

/-- One merged multiproof for tree `kind` (0 = C1, 1 = C2, 2 = folded). -/
def verifyMerged (p : Parsed) (q : Fin 22 → Fin 262144) (kind : Nat) :
    Program Bytes State Bool :=
  slotB 22 (mergedCapacity kind) (mergedStart kind) (sortedAll q kind) p q kind

def mergedPrograms (p : Parsed) (q : Fin 22 → Fin 262144) : List (Program Bytes State Bool) :=
  [0,1,2].map (verifyMerged p q)

/-- The three merged multiproofs, short-circuited in tree order (merged_merkle,
fused.rs:800-806). -/
def verifyMergedAll (p : Parsed) (q : Fin 22 → Fin 262144) : Program Bytes State Bool :=
  OraclePortShortCircuit.short (mergedPrograms p q)

theorem sortedAll_mem (q : Fin 22 → Fin 262144) (kind pos : Nat) (h : pos < 22) :
    pos ∈ sortedAll q kind := by
  simpa only [sortedAll,List.mem_mergeSort,List.mem_range] using h

/-! ### Paths: copies of R1's `inPlace_success`, `inPlace_path`, `slot_path` -/

theorem inPlaceB_success (n : Nat) (H : Bytes → State) (root : State) (live : Live) (nodes : Bytes)
    (accepted : (eval H (verifyInPlaceB n root live nodes)).2 = true) :
    (eval H (runLevels 18 live nodes)).2 = some ([(0,root)],[]) := by
  unfold verifyInPlaceB at accepted
  split at accepted
  · simp only [eval_bind,eval] at accepted
    split at accepted
    · rename_i i d remaining out
      have ok : i=0 ∧ d=root ∧ remaining=[] := of_decide_eq_true accepted
      rcases ok with ⟨rfl,rfl,rfl⟩
      exact out
    · contradiction
  · contradiction

theorem inPlaceB_path (n : Nat) (H : Bytes → State) (root : State) (live : Live) (nodes : Bytes)
    (accepted : (eval H (verifyInPlaceB n root live nodes)).2 = true)
    (i : Nat) (v : State) (member : (i,v) ∈ live) :
    ∃ path : Path (BinMultiproof.slots 18 i), foldPath H path v = root ∧
      ∀ a ∈ inputTrace H path v, Read (eval H (verifyInPlaceB n root live nodes)).1 a := by
  have success := inPlaceB_success n H root live nodes accepted
  obtain ⟨path,hm,hr⟩ := levels_path H 18 live nodes [(0,root)] [] success i v member
  have eq : foldPath H path v = root := by simpa using congrArg Prod.snd (List.mem_singleton.mp hm)
  refine ⟨path,eq,?_⟩
  unfold verifyInPlaceB at accepted ⊢
  split
  · simpa only [eval_bind,eval,List.append_nil] using hr
  · rename_i bad
    simp only [if_neg bad,eval,Bool.false_eq_true] at accepted

theorem slotB_path (n cap start : Nat) (ps : List Nat) (H : Bytes → State) (p : Parsed)
    (q : Fin 22 → Fin 262144) (kind pos : Nat) (member : pos ∈ ps)
    (accepted : (eval H (slotB n cap start ps p q kind)).2 = true) :
    ∃ path : Path (BinMultiproof.slots 18 (index q kind pos)),
      foldPath H path (H (leaf p kind pos)) = committedRoot p kind ∧
      ∀ a ∈ BinMerkle32Leaf.fullTrace H path (leaf p kind pos),
        Read (eval H (slotB n cap start ps p q kind)).1 a := by
  simp only [slotB,eval_bind] at accepted ⊢
  cases out : (eval H (hashLeaves p q kind ps [])).2 with
  | none => simp [out,eval] at accepted
  | some live =>
    simp only [out] at accepted ⊢
    have retained := (leaves_retained H p q kind ps [] live out).2 pos member
    unfold tailB at accepted ⊢
    dsimp only at accepted ⊢
    split
    · rename_i wf
      simp only [if_pos wf] at accepted
      split
      · rename_i pad
        simp only [if_pos pad] at accepted
        obtain ⟨path,root,reads⟩ := inPlaceB_path n H (committedRoot p kind) live _ accepted
          (index q kind pos) (H (leaf p kind pos)) retained.1
        refine ⟨path,root,?_⟩
        intro a ha
        simp only [BinMerkle32Leaf.fullTrace,List.mem_cons] at ha
        simp only [Read,List.map_append,List.mem_append]
        rcases ha with rfl | ha
        · exact Or.inl retained.2
        · exact Or.inr (reads a ha)
      · rename_i pad
        simp [pad,eval] at accepted
    · rename_i wf
      simp [wf,eval] at accepted

/-- Check: R1's `slot_path`, re-derived from the generic theorem. -/
theorem r1_slot_path_check (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch kind pos : Nat) (member : pos ∈ batchPositions batch)
    (accepted : (eval H (verifySlot_frozen p q batch kind)).2 = true) :
    ∃ path : Path (BinMultiproof.slots 18 (index q kind pos)),
      foldPath H path (H (leaf p kind pos)) = committedRoot p kind ∧
      ∀ a ∈ BinMerkle32Leaf.fullTrace H path (leaf p kind pos),
        Read (eval H (verifySlot_frozen p q batch kind)).1 a := by
  rw [r1_slot_instance] at accepted ⊢
  exact slotB_path _ _ _ _ H p q kind pos
    (by simpa only [sortedPositions,List.mem_mergeSort] using member) accepted

/-! ### Recovery at the queried index: copy of R1's `recovery_at_index` -/

theorem slotB_recovery_at_index (n cap start : Nat) (ps : List Nat) (H : Bytes → State)
    (p : Parsed) (q : Fin 22 → Fin 262144) (kind pos : Nat) (member : pos ∈ ps)
    (accepted : (eval H (slotB n cap start ps p q kind)).2 = true)
    (tr : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ tr, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (slotB n cap start ps p q kind)).1 a → Read tr a)
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
  obtain ⟨path,root,reads⟩ := slotB_path n cap start ps H p q kind pos member accepted
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

/-- Check: R1's `recovery_at_index` (OraclePortFrozenOrderCutRecovery), with its
exact hypotheses, re-derived from the generic theorem. -/
theorem r1_recovery_at_index_check (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
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
  rw [r1_slot_instance] at accepted contains
  exact slotB_recovery_at_index _ _ _ _ H p q kind pos
    (by simpa only [sortedPositions,List.mem_mergeSort] using member) accepted tr Q consistent
    contains bound clean frame j frameRead rootRead tag width packed salt leafBytes packedWidth saltWidth

/-- The merged slot, per position: every one of the 22 queried positions of tree
`kind` is recovered from the log cut at its root's commitment frame. -/
theorem merged_recovery_at_index (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (kind pos : Nat) (posBound : pos < 22)
    (accepted : (eval H (verifyMerged p q kind)).2 = true)
    (tr : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ tr, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (verifyMerged p q kind)).1 a → Read tr a)
    (bound : firstReads emptyTable tr ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable tr)
    (frame : Bytes) (j : Fin 5) (frameRead : Read tr frame)
    (rootRead : BinRawByteCollisionTargets.pred j frame = some (committedRoot p kind))
    (tag : BinMerkle32Path.Byte) (width : Nat) (packed salt : Bytes)
    (leafBytes : leaf p kind pos = BinMerkle32Leaf.leafInput tag packed salt)
    (packedWidth : packed.length = width) (saltWidth : salt.length = 32) :
    BinRawByteCutStability.recoverAt tag width (BinRawByteCutRecovery.cut tr frame)
      (BinMultiproof.slots 18 (index q kind pos)) (committedRoot p kind) = some (packed,salt) :=
  slotB_recovery_at_index _ _ _ _ H p q kind pos (sortedAll_mem q kind pos posBound) accepted
    tr Q consistent contains bound clean frame j frameRead rootRead tag width packed salt
    leafBytes packedWidth saltWidth

#print axioms r1_slot_instance
#print axioms inPlaceB_success
#print axioms inPlaceB_path
#print axioms slotB_path
#print axioms r1_slot_path_check
#print axioms slotB_recovery_at_index
#print axioms r1_recovery_at_index_check
#print axioms merged_recovery_at_index
end AspisOneTx
end
