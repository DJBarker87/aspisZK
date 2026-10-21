import OraclePortCoverageDraft

set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortDuplicateBindingDraft
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft

/-- Successful lookup in the retained table refers to an actual tree read. -/
theorem retained_read (H : Bytes → State) (t : OracleDecisionMultiTree.Tree)
    (a : Bytes × State) (ha : a ∈ (eval H (execute t)).2.2) :
    Read (eval H (execute t)).1 a.1 := by
  induction t with
  | supplied d => simp [execute,eval] at ha
  | opened input =>
    simp only [execute,eval,List.mem_singleton] at ha
    subst a
    exact List.mem_cons_self ..
  | branch l r il ir =>
    simp only [Read,execute,eval_bind,eval,List.map_append,List.mem_append] at ha ⊢
    rcases ha with hl | hr
    · have h := il hl
      exact Or.inl h
    · have h := ir hr
      exact Or.inr (Or.inl h)

theorem duplicate_lookup (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch kind : Nat) (known : List (Bytes × State)) (ps : List Nat)
    (ha : (eval H (duplicates p q batch kind known ps)).2 = true)
    (pos : Nat) (hp : pos ∈ ps) :
    known.lookup (input p q batch kind (index q kind pos)) = some (H (leaf p kind pos)) := by
  induction ps with
  | nil => simp at hp
  | cons head rest ih =>
    simp only [duplicates,eval,eval_bind,Bool.and_eq_true,decide_eq_true_eq] at ha
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ha.1
    · exact ih ha.2 hp

theorem duplicate_read (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch kind : Nat) (known : List (Bytes × State)) (ps : List Nat)
    (pos : Nat) (hp : pos ∈ ps) :
    Read (eval H (duplicates p q batch kind known ps)).1 (leaf p kind pos) := by
  induction ps with
  | nil => simp at hp
  | cons head rest ih =>
    simp only [duplicates,eval,eval_bind]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (by simpa only [List.append_nil] using (show leaf p kind pos ∈ (eval H (duplicates p q batch kind known rest)).1.map Prod.fst from ih hp))

/-- The raw five-reader collision event, on an explicitly containing trace,
upgrades the actual duplicate digest comparison to byte equality. -/
theorem slot_duplicate_bytes (H : Bytes → State) (p : Parsed)
    (q : Fin 22 → Fin 262144) (batch kind pos : Nat)
    (hp : pos ∈ duplicatePositions q batch kind)
    (ha : (eval H (verifySlot p q batch kind)).2 = true)
    (tr : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ tr, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (verifySlot p q batch kind)).1 a → Read tr a)
    (bound : firstReads emptyTable tr ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable tr) :
    leaf p kind pos = input p q batch kind (index q kind pos) := by
  let t := tree p q batch kind
  let known := (eval H (execute t)).2.2
  have ha' : (eval H (duplicates p q batch kind known (duplicatePositions q batch kind))).2 = true := by
    simp only [verifySlot,eval_bind,eval,Bool.and_eq_true] at ha
    exact ha.2
  have lookup := duplicate_lookup H p q batch kind known _ ha' pos hp
  have mem : (input p q batch kind (index q kind pos),H (leaf p kind pos)) ∈ known := by
    obtain ⟨l1,l2,he,_⟩ := List.lookup_eq_some_iff.mp lookup
    rw [he]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have same := retained_consistent H t _ mem
  have hr : Read tr (input p q batch kind (index q kind pos)) := by
    apply contains
    have ht := retained_read H t _ mem
    simp only [Read,verifySlot,eval_bind,eval,List.append_nil,List.map_append,List.mem_append]
    exact Or.inl ht
  have hd : Read tr (leaf p kind pos) := by
    apply contains
    have ht := duplicate_read H p q batch kind known _ pos hp
    simp only [Read,verifySlot,eval_bind,eval,List.append_nil,List.map_append,List.mem_append]
    exact Or.inr ht
  by_contra different
  exact AllAddressCollisionTrace.outputs_injective _ _ H tr Q consistent bound clean
    _ _ hd hr different same

#print axioms retained_read
#print axioms duplicate_lookup
#print axioms duplicate_read
#print axioms slot_duplicate_bytes
end AspisR1.OraclePortDuplicateBindingDraft
end
