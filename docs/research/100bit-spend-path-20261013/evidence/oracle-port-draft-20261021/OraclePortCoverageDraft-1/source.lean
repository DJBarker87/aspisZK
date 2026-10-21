import OraclePortBatchDraft

set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCoverageDraft
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OracleDecisionMultiTree OracleDecisionMultiBuild
open OracleDecisionMultiRecovery (OpenedAt)

/-- The sibling-slot count is proved on the sparse tree, not by reduction of
18 concrete recurrence layers. -/
theorem frontier_count (is : List Nat) (f : Nat → Bytes) (s : Nat → Nat → State)
    (h base : Nat) : (frontier is h base).length = siblings (build is f s h base) := by
  induction h generalizing base with
  | zero => by_cases ho : Occupied is 0 base <;> simp [frontier,build,ho,siblings]
  | succ h ih =>
    by_cases ho : Occupied is (h+1) base
    · simp only [frontier,build,if_pos ho,List.length_append,siblings,ih]
    · simp [frontier,build,ho,siblings]

theorem ordered_count (is : List Nat) (f : Nat → Bytes) (s : Nat → Nat → State) :
    (orderedFrontier is).length = siblings (build is f s 18 0) := by
  rw [orderedFrontier,List.length_mergeSort]
  exact frontier_count is f s 18 0

theorem padding_bounds (p : Parsed) (q : Fin 22 → Fin 262144) (hp : Padding p q)
    (batch kind : Nat) (hb : batch ∈ List.range 2) (hk : kind ∈ List.range 3) :
    siblings (tree p q batch kind) ≤ capacity (3*batch+kind) := by
  rw [tree,← ordered_count]
  exact (hp batch hb kind hk).1

def forest (p : Parsed) (q : Fin 22 → Fin 262144) : List Commitment :=
  slots.map (fun bk => ⟨tree p q bk.1 bk.2,committedRoot p bk.2⟩)

theorem forest_six (p : Parsed) (q : Fin 22 → Fin 262144) :
    (forest p q).length = 6 := by rfl

theorem forest_occupied (p : Parsed) (q : Fin 22 → Fin 262144)
    (c : Commitment) (hc : c ∈ forest p q) : 0 < leaves c.tree := by
  obtain ⟨bk,_,rfl⟩ := List.mem_map.mp hc
  exact occupied_tree p q bk.1 bk.2

/-- This construction excludes the earlier supplied-only counterexample
without an acceptance assumption. Every selected index has a real leaf. -/
theorem selected_opened (p : Parsed) (q : Fin 22 → Fin 262144)
    (batch kind pos : Nat) (hp : pos ∈ batchPositions batch) :
    ∃ path, path.length = 18 ∧
      OpenedAt (tree p q batch kind) path (input p q batch kind (index q kind pos)) := by
  apply build_opened
  · exact List.mem_map.mpr ⟨pos,hp,rfl⟩
  · exact Nat.zero_le _
  · unfold index
    dsimp only
    split
    · have ht := (q ⟨pos % 22,Nat.mod_lt _ (by decide)⟩).isLt
      dsimp only
      omega
    · exact (q _).isLt

#print axioms frontier_count
#print axioms ordered_count
#print axioms padding_bounds
#print axioms forest_six
#print axioms forest_occupied
#print axioms selected_opened
end AspisR1.OraclePortCoverageDraft
end
