import BinBatchDedup

/-! Exact read-set coverage for the existing binary relational model.
This module does not assert correspondence of the extracted array loops. -/
set_option autoImplicit false
namespace AspisR1.R13MultiproofReadSet
open BinMerkle32Path BinMultiproof
open AspisV8R19.MemoizedProgramLaw

/-- A coherent family, including coverage in the reverse direction: every
multiproof read belongs to a path of an occupied initial index. -/
theorem accepted_family {H : List Byte → Digest} {root : Digest}
    {depth : Nat} {active : Active} {v : Values} {nodes : List Digest}
    {trace : List (List Byte)} (h : Accept H root depth active v nodes trace) :
    ∃ paths : (i : Nat) → i ∈ active → Path (slots depth i),
      (∀ i hi, foldPath H (paths i hi) (v i) = root ∧
        inputTrace H (paths i hi) (v i) ⊆ trace) ∧
      (∀ input, input ∈ trace ↔ ∃ i, ∃ hi : i ∈ active,
        input ∈ inputTrace H (paths i hi) (v i)) := by
  induction h with
  | done v hroot =>
      refine ⟨fun _ _ => .nil, ?_, ?_⟩
      · intro i hi
        have he : i = 0 := by simpa using hi
        subst i
        exact ⟨hroot, by simp [slots, inputTrace]⟩
      · intro input
        simp [slots, inputTrace]
  | @step depth active v cs supplied rest trace level tail ih =>
      obtain ⟨ps, hp, cover⟩ := ih
      let paths : (i : Nat) → i ∈ active → Path (slots (depth + 1) i) :=
        fun i hi => .cons (cs (i / 2)) (ps (i / 2) (member_parent hi))
      have hc : ∀ i ∈ active, fillChild (slot i) (cs (i / 2)) (v i) = cs (i / 2) := by
        intro i hi
        rw [← level.1 i hi]
        exact Function.update_eq_self _ _
      have path_trace : ∀ i (hi : i ∈ active),
          inputTrace H (paths i hi) (v i) = nodeInput (cs (i / 2)) ::
            inputTrace H (ps (i / 2) (member_parent hi)) (nextValues H cs (i / 2)) := by
        intro i hi
        simp only [paths, slots, inputTrace, hc i hi, nextValues]
      have good : ∀ i hi, foldPath H (paths i hi) (v i) = root ∧
          inputTrace H (paths i hi) (v i) ⊆ levelInputs active cs ++ trace := by
        intro i hi
        constructor
        · simpa only [paths, slots, foldPath, hc i hi, nextValues] using (hp (i / 2) (member_parent hi)).1
        · rw [path_trace i hi]
          intro input hin
          rcases List.mem_cons.mp hin with he | ht
          · apply List.mem_append_left
            subst input
            exact List.mem_map.mpr ⟨i / 2, by simpa using member_parent hi, rfl⟩
          · exact List.mem_append_right _ ((hp _ _).2 ht)
      refine ⟨paths, good, ?_⟩
      intro input
      constructor
      · intro hin
        rcases List.mem_append.mp hin with hhead | htail
        · obtain ⟨p, hparent, he⟩ := List.mem_map.mp hhead
          have hparent' : p ∈ parents active := by simpa using hparent
          obtain ⟨i, hi, hip⟩ := Finset.mem_image.mp hparent'
          refine ⟨i, hi, ?_⟩
          rw [path_trace i hi]
          exact List.mem_cons.mpr (Or.inl (by simpa only [hip] using he.symm))
        · obtain ⟨p, hparent, hm⟩ := (cover input).mp htail
          obtain ⟨i, hi, hip⟩ := Finset.mem_image.mp hparent
          subst p
          refine ⟨i, hi, ?_⟩
          rw [path_trace i hi]
          exact List.mem_cons_of_mem _ hm
      · rintro ⟨i, hi, hm⟩
        exact (good i hi).2 hm

/-- Dedup composition for every original query, now with executable program
acceptance. It retains the model's exact leaf digest and index. -/
theorem original_query_programs {H : List Byte → Digest} {root : Digest}
    {depth : Nat} {active : Active} {v : Values} {nodes : List Digest}
    {trace : List (List Byte)} {batch canonical : List BinBatchDedup.Entry}
    (hrun : BinBatchDedup.run batch = some canonical)
    (hrep : Dedup canonical active v)
    (h : Accept H root depth active v nodes trace) :
    ∀ q ∈ batch, ∃ path : Path (slots depth q.1),
      (eval H (BinMerkleProgram.pathProgram path q.2)).2 = root ∧
      inputTrace H path q.2 ⊆ trace := by
  intro q hq
  obtain ⟨path, hp, ht⟩ := BinBatchDedup.accepted_original_queries hrun hrep h q hq
  exact ⟨path, (BinMerkleProgram.pathProgram_accepts_iff H path q.2 root).mpr hp, ht⟩

/-- The parent at level `level` has the requested original-index geometry. -/
theorem parent_geometry (u level : Nat) :
    (u / 2 ^ level) / 2 = u / 2 ^ (level + 1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

#print axioms accepted_family
#print axioms original_query_programs
#print axioms parent_geometry
end AspisR1.R13MultiproofReadSet
