import R1Z.ProverCommitSorted32
set_option autoImplicit false
namespace R1Z.ProverCommitMapInvariant32
open Aeneas.Std R1Z.ProverCommitPublication32 R1Z.ProverCommitSorted32

theorem insert_mem (key : Usize) (value : Bytes) (xs : List (Usize × Bytes))
    (entry : Usize × Bytes) (h : entry ∈ (R1Z.ProverCommitSorted32.insert key value xs).1) :
    entry=(key,value) ∨ entry ∈ xs := by
  induction xs generalizing entry with
  | nil =>
    left
    simpa only [R1Z.ProverCommitSorted32.insert,List.mem_singleton] using h
  | cons first xs ih =>
    rcases first with ⟨k,v⟩
    by_cases lt : key<k
    · simpa only [R1Z.ProverCommitSorted32.insert,if_pos lt,List.mem_cons] using h
    · by_cases eq : key=k
      · simp only [R1Z.ProverCommitSorted32.insert,if_neg lt,if_pos eq,List.mem_cons] at h
        rcases h with h|h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · simp only [R1Z.ProverCommitSorted32.insert,if_neg lt,if_neg eq,List.mem_cons] at h
        rcases h with h|h
        · exact Or.inr (List.mem_cons.mpr (Or.inl h))
        · rcases ih entry h with fresh|old
          · exact Or.inl fresh
          · exact Or.inr (List.mem_cons_of_mem _ old)

/-- Strict key ordering, hence uniqueness and iteration order, is preserved
by every source-specified insertion, starting from the empty association list. -/
theorem insert_sorted (key : Usize) (value : Bytes) (xs : List (Usize × Bytes))
    (sorted : xs.Pairwise (fun a b => a.1 < b.1)) :
    (R1Z.ProverCommitSorted32.insert key value xs).1.Pairwise (fun a b => a.1 < b.1) := by
  revert sorted
  induction xs with
  | nil =>
    intro _
    simp [R1Z.ProverCommitSorted32.insert]
  | cons first xs ih =>
    rcases first with ⟨k,v⟩
    intro sorted
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp sorted
    by_cases lt : key<k
    · simp only [R1Z.ProverCommitSorted32.insert,if_pos lt]
      apply List.pairwise_cons.mpr
      refine ⟨?_,sorted⟩
      intro e he
      rcases List.mem_cons.mp he with equal|member
      · rw [equal];exact lt
      · exact lt_trans lt (head e member)
    · by_cases eq : key=k
      · simp only [R1Z.ProverCommitSorted32.insert,if_neg lt,if_pos eq]
        apply List.pairwise_cons.mpr
        exact ⟨by simpa only [eq] using head,tail⟩
      · simp only [R1Z.ProverCommitSorted32.insert,if_neg lt,if_neg eq]
        apply List.pairwise_cons.mpr
        refine ⟨?_,ih tail⟩
        intro e he
        rcases insert_mem key value xs e he with equal|member
        · rw [equal]
          exact lt_of_le_of_ne (le_of_not_gt lt) (Ne.symm eq)
        · exact head e member

#print axioms insert_mem
#print axioms insert_sorted
end R1Z.ProverCommitMapInvariant32
