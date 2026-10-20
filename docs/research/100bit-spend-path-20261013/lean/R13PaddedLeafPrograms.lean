import R13MultiproofReadSet
set_option autoImplicit false
namespace AspisR1.R13PaddedLeafPrograms
open BinMerkle32Path BinMultiproof
open AspisV8R19.MemoizedProgramLaw

/-- Model consumer for the source simulation: padding cannot supply a sibling,
and every original (including duplicated) opening has an accepted leaf
program on the same index and root. `hrun` concerns the Bin dedup model;
equality with the source's sorted-key scan must be proved separately. -/
theorem padded_leaf_programs {H : List Byte → Digest} {root : Digest}
    {depth : Nat} {active : Active} {v : Values} {count capacity : Nat}
    {stored : List Digest} {trace : List (List Byte)}
    {queries : List (Nat × List Byte)} {canonical : List BinBatchDedup.Entry}
    (hrun : BinBatchDedup.run (queries.map fun q => (q.1, H q.2)) = some canonical)
    (hrep : Dedup canonical active v)
    (h : PaddedAccept H root depth active v count capacity stored trace) :
    count = nodeCount depth active ∧
      ∀ q ∈ queries, ∃ path : Path (slots depth q.1),
        (eval H (BinMerkleProgram.leafProgram path q.2)).2 = root ∧
        BinMerkle32Leaf.fullTrace H path q.2 ⊆ queries.map Prod.snd ++ trace := by
  refine ⟨padded_exact_count h, ?_⟩
  intro q hq
  have hpair : (q.1, H q.2) ∈ queries.map (fun q => (q.1, H q.2)) :=
    List.mem_map.mpr ⟨q, hq, rfl⟩
  obtain ⟨path, hp, ht⟩ := BinBatchDedup.accepted_original_queries hrun hrep h.2.2.2 _ hpair
  refine ⟨path, (BinMerkleProgram.leafProgram_accepts_iff H path q.2 root).mpr hp, ?_⟩
  intro input hin
  rcases List.mem_cons.mp hin with he | hm
  · apply List.mem_append_left
    subst input
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  · exact List.mem_append_right _ (ht hm)

#print axioms padded_leaf_programs
end AspisR1.R13PaddedLeafPrograms
