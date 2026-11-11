import AspisOneTxMergedSlot
import OraclePortFrozen2Resource

/-! The Aspis one-transaction verifier: issued digest calls of the merged
multiproofs (item M3 of ONE-TRANSACTION-GAME.md).

Kind of result: MODEL THEOREMS (all-input issued-call bounds of oracle
programs, rejections included). Copies of `OraclePortFrozen2Resource.inPlace`,
`.tail` and `.slot` for the generic slot `slotB`, using R1's `levels` and
`leaves_bound` unchanged. R1's `slot` bound is re-derived as a check. For the
merged slots the bound `2·22 + cap − 1` gives 339, 339 and 297, and the three
short-circuited slots issue at most 975 digest calls on every input.

NOT established here: the 40-row sampler-prefix count (136, PAPER) and hence
the verifier total (1,111, PAPER); both need the Aspis model decision and the
40-row sampler. -/
set_option autoImplicit false
noncomputable section
namespace AspisOneTx
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1 AspisR1.OraclePortCompactDraft AspisR1.OraclePortSelectedDraft
open AspisR1.OraclePortBatchDraft AspisR1.OraclePortFrozenOrder AspisR1.OraclePortFrozen2Resource
attribute [local instance] Classical.propDecidable

theorem inPlaceB_bound (n : Nat) (H : Bytes → State) (root : State) (live : Live) (nodes : Bytes)
    (nonempty : live ≠ []) :
    (eval H (verifyInPlaceB n root live nodes)).1.length + 1 ≤ live.length + nodes.length / 32 := by
  have positive : 0 < live.length := List.length_pos_iff.mpr nonempty
  unfold verifyInPlaceB
  split
  · have bound := levels H 18 live nodes
    have one : 1 ≤ potential (eval H (runLevels 18 live nodes)).2 := le_max_left _ _
    simp only [eval_bind,eval,List.append_nil]
    omega
  · simp only [eval,List.length_nil]; omega

theorem tailB_bound_strict (n cap start : Nat) (H : Bytes → State) (p : Parsed) (kind : Nat)
    (live : Live) (cap_pos : 0 < cap) :
    (eval H (tailB n cap start p kind live)).1.length + 1 ≤ live.length + cap := by
  unfold tailB
  dsimp only
  split
  · rename_i formed
    have nonempty : live ≠ [] := by
      intro empty
      apply formed.1
      simp only [empty,List.map_nil]
    split
    · have bound := inPlaceB_bound n H (committedRoot p kind) live
        ((slice p.wire start (32*cap)).take (32*nodeCount 18 (live.map Prod.fst))) nonempty
      have len : ((slice p.wire start (32*cap)).take
          (32*nodeCount 18 (live.map Prod.fst))).length / 32 ≤ cap := by
        rw [List.length_take]; omega
      omega
    · simp only [eval,List.length_nil]; omega
  · simp only [eval,List.length_nil]; omega

/-- Generic slot bound: leaves plus capacity, minus one. -/
theorem slotB_bound (n cap start : Nat) (ps : List Nat) (H : Bytes → State) (p : Parsed)
    (q : Fin 22 → Fin 262144) (kind : Nat) (cap_pos : 0 < cap) :
    (eval H (slotB n cap start ps p q kind)).1.length + 1 ≤ 2*ps.length + cap := by
  have bound := leaves_bound H p q kind ps []
  simp only [slotB,eval_bind,List.length_append]
  cases out : (eval H (hashLeaves p q kind ps [])).2 with
  | none => simp only [eval,List.length_nil]; omega
  | some live =>
    have tb := tailB_bound_strict n cap start H p kind live cap_pos
    simp only [out,leafWeight,List.length_nil,Nat.add_zero] at bound
    simp only
    omega

/-- Check: R1's `OraclePortFrozen2Resource.slot`, re-derived. -/
theorem r1_slot_bound_check (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch kind : Nat) (cap : 0 < capacity (3*batch+kind)) :
    (eval H (verifySlot_frozen p q batch kind)).1.length + 1 ≤
      2*(batchPositions batch).length + capacity (3*batch+kind) := by
  have len : (sortedPositions q batch kind).length = (batchPositions batch).length :=
    List.length_mergeSort ..
  rw [r1_slot_instance, ← len]
  exact slotB_bound _ _ _ _ H p q kind cap

theorem sortedAll_length (q : Fin 22 → Fin 262144) (kind : Nat) : (sortedAll q kind).length = 22 := by
  simp only [sortedAll,List.length_mergeSort,List.length_range]

/-- Merged slot bound: `2·22 + mergedCapacity kind − 1`. -/
theorem merged_bound (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144) (kind : Nat)
    (hk : kind < 3) :
    (eval H (verifyMerged p q kind)).1.length + 1 ≤ 44 + mergedCapacity kind := by
  have pos : 0 < mergedCapacity kind := by interval_cases kind <;> decide
  have h := slotB_bound 22 (mergedCapacity kind) (mergedStart kind) (sortedAll q kind) H p q kind pos
  rw [sortedAll_length] at h
  exact h

theorem merged_bound_values (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144) :
    (eval H (verifyMerged p q 0)).1.length ≤ 339 ∧
    (eval H (verifyMerged p q 1)).1.length ≤ 339 ∧
    (eval H (verifyMerged p q 2)).1.length ≤ 297 := by
  have h0 := merged_bound H p q 0 (by decide)
  have h1 := merged_bound H p q 1 (by decide)
  have h2 := merged_bound H p q 2 (by decide)
  have c0 : mergedCapacity 0 = 296 := rfl
  have c1 : mergedCapacity 1 = 296 := rfl
  have c2 : mergedCapacity 2 = 254 := rfl
  rw [c0] at h0; rw [c1] at h1; rw [c2] at h2
  exact ⟨by omega, by omega, by omega⟩

/-- A short-circuited list issues at most the sum of its members' calls. -/
theorem short_length (H : Bytes → State) (ps : List (Program Bytes State Bool)) :
    (eval H (OraclePortShortCircuit.short ps)).1.length ≤
      (ps.map fun x => (eval H x).1.length).sum := by
  induction ps with
  | nil => simp [OraclePortShortCircuit.short,eval]
  | cons x xs ih =>
    simp only [OraclePortShortCircuit.short,eval_bind,List.map_cons,List.sum_cons,List.length_append]
    cases (eval H x).2
    · simp only [Bool.false_eq_true,if_false,eval,List.length_nil]; omega
    · simp only [if_true]; omega

/-- All-input issued-call budget of the three merged multiproofs: 975
(= 66 leaf hashes + at most 909 parents), rejections included. -/
theorem mergedAll_budget (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144) :
    (eval H (verifyMergedAll p q)).1.length ≤ 975 := by
  have hs := short_length H (mergedPrograms p q)
  obtain ⟨h0,h1,h2⟩ := merged_bound_values H p q
  simp only [verifyMergedAll,mergedPrograms,List.map_cons,List.map_nil] at hs ⊢
  simp only [List.sum_cons,List.sum_nil] at hs
  omega

#print axioms inPlaceB_bound
#print axioms tailB_bound_strict
#print axioms slotB_bound
#print axioms r1_slot_bound_check
#print axioms merged_bound
#print axioms merged_bound_values
#print axioms short_length
#print axioms mergedAll_budget
end AspisOneTx
end
