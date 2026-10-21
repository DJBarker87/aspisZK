import OraclePortRepresentativeCountC3
import OraclePortPhysicalFrameDraft

/-! The 66 source leaf calls are representative leaves plus duplicate calls,
including rejected/collision executions. Padding is checked before hashing. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortSixSlotBudgetC3
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortCoverageDraft OraclePortRepresentativeCountC3
open OracleDecisionMultiTree (leaves parents siblings binary_count)

def duplicateCount (q : Fin 22 → Fin 262144) (ss : List (Nat × Nat)) : Nat :=
  ((ss.map fun bk => (duplicatePositions q bk.1 bk.2).length)).sum

theorem leaf_count (p : Parsed) (q : Fin 22 → Fin 262144) :
    OracleDecisionMultiTree.totalLeaves (forest p q) + duplicateCount q slots = 66 := by
  have h00 := slot_leaf_law p q 0 0
  have h01 := slot_leaf_law p q 0 1
  have h02 := slot_leaf_law p q 0 2
  have h10 := slot_leaf_law p q 1 0
  have h11 := slot_leaf_law p q 1 1
  have h12 := slot_leaf_law p q 1 2
  have ha : (batchPositions 0).length = 10 := by rfl
  have hb : (batchPositions 1).length = 12 := by rfl
  rw [ha] at h00 h01 h02
  rw [hb] at h10 h11 h12
  simp only [OracleDecisionMultiTree.totalLeaves,forest,slots,duplicateCount,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

theorem verifySlot_length (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch kind : Nat) :
    (eval H (verifySlot p q batch kind)).1.length =
      leaves (tree p q batch kind) + parents (tree p q batch kind) +
        (duplicatePositions q batch kind).length := by
  simp only [verifySlot,eval_bind,eval,List.append_nil,List.length_append,duplicates_length]
  rw [(execute_trace H (tree p q batch kind)).1,
    OracleDecisionMultiTree.execute_length]

theorem verifySlots_length (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (ss : List (Nat × Nat)) :
    (eval H (verifySlots p q ss)).1.length =
      ((ss.map fun bk => leaves (tree p q bk.1 bk.2) + parents (tree p q bk.1 bk.2) +
        (duplicatePositions q bk.1 bk.2).length)).sum := by
  induction ss with
  | nil => rfl
  | cons bk rest ih =>
    simp only [verifySlots,eval_bind,eval,List.append_nil,List.length_append,
      verifySlot_length,ih,List.map_cons,List.sum_cons]

theorem six_slot_length (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144) :
    (eval H (verifySlots p q slots)).1.length =
      66 + OracleDecisionMultiTree.totalParents (forest p q) := by
  rw [verifySlots_length]
  have hc := leaf_count p q
  simp only [OracleDecisionMultiTree.totalLeaves,OracleDecisionMultiTree.totalParents,
    forest,slots,duplicateCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at *
  omega

theorem sibling_bound (p : Parsed) (q : Fin 22 → Fin 262144) (hp : Padding p q) :
    OracleDecisionMultiTree.totalSiblings (forest p q) ≤ 914 := by
  have h00 := padding_bounds p q hp 0 0 (by decide) (by decide)
  have h01 := padding_bounds p q hp 0 1 (by decide) (by decide)
  have h02 := padding_bounds p q hp 0 2 (by decide) (by decide)
  have h10 := padding_bounds p q hp 1 0 (by decide) (by decide)
  have h11 := padding_bounds p q hp 1 1 (by decide) (by decide)
  have h12 := padding_bounds p q hp 1 2 (by decide) (by decide)
  change siblings (tree p q 0 0) ≤ 146 at h00
  change siblings (tree p q 0 1) ≤ 146 at h01
  change siblings (tree p q 0 2) ≤ 128 at h02
  change siblings (tree p q 1 0) ≤ 172 at h10
  change siblings (tree p q 1 1) ≤ 172 at h11
  change siblings (tree p q 1 2) ≤ 150 at h12
  simp only [OracleDecisionMultiTree.totalSiblings,forest,slots,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

theorem batch_budget (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (hp : Padding p q) : (eval H (verifySlots p q slots)).1.length ≤ 1040 := by
  have hf := OracleDecisionMultiTree.forest_count (forest p q)
  have hs := sibling_bound p q hp
  have hl := leaf_count p q
  have hn := forest_six p q
  rw [six_slot_length]
  omega

/-- Six actual write/resume frame calls leave the terminal at most 1046. -/
theorem terminal_budget (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (hp : Padding p q) (frameCalls : Nat) (hframe : frameCalls ≤ 6) :
    frameCalls + (eval H (verifySlots p q slots)).1.length ≤ 1046 := by
  have hb := batch_budget H p q hp
  omega

/-- Explicit helper composition; it is not the completed verifier because the
stored proof cannot yet reach the inherited decision carrier. -/
def checkpointBatch (proof pub ck : Bytes) (p : Parsed) (q : Fin 22 → Fin 262144) :
    Program Bytes State Bool :=
  bind (OraclePortPhysicalFrameDraft.writeResume proof pub ck) fun checkpointOK =>
    bind (verifySlots p q slots) fun batchOK => .done (checkpointOK && batchOK)

theorem checkpointBatch_budget (H : Bytes → State) (proof pub ck : Bytes)
    (p : Parsed) (q : Fin 22 → Fin 262144) (hp : Padding p q) :
    (eval H (checkpointBatch proof pub ck p q)).1.length ≤ 1046 := by
  have hf : (eval H (OraclePortPhysicalFrameDraft.writeResume proof pub ck)).1.length ≤ 6 := by
    by_cases hs : OraclePortPhysicalFrameDraft.Shape ck
    · exact le_of_eq (OraclePortPhysicalFrameDraft.six_frames H proof pub ck hs)
    · simp only [OraclePortPhysicalFrameDraft.writeResume,OraclePortPhysicalFrameDraft.check,
        if_neg hs,eval_bind,eval,List.append_nil,List.length_nil]
      omega
  have hb := batch_budget H p q hp
  simp only [checkpointBatch,eval_bind,eval,List.append_nil,List.length_append]
  omega

#print axioms leaf_count
#print axioms verifySlot_length
#print axioms verifySlots_length
#print axioms six_slot_length
#print axioms sibling_bound
#print axioms batch_budget
#print axioms terminal_budget
#print axioms checkpointBatch_budget
end AspisR1.OraclePortSixSlotBudgetC3
end
