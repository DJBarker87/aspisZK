import R1MerkleLeafRecovery

/-! Extensionality for recorded-leaf lookups. Membership equivalence and
per-digest uniqueness are explicit; no hash or recovery premise is used. -/
set_option autoImplicit false
namespace AspisR1.MerkleLeafLookupExt

open AspisR1.MerkleLeafRecovery

private theorem lookupLeaf_exists_mem {leaves : Leaves} {data : LeafData}
    {digest : Digest} (hin : (data, digest) ∈ leaves) :
    ∃ found, lookupLeaf leaves digest = some found := by
  induction leaves with
  | nil => simp at hin
  | cons entry rest ih =>
      rcases entry with ⟨head, output⟩
      rcases List.mem_cons.mp hin with heq | htail
      · cases heq
        exact ⟨data, by simp [lookupLeaf]⟩
      · obtain ⟨found, hfound⟩ := ih htail
        by_cases ho : output = digest
        · exact ⟨head, by simp [lookupLeaf, ho]⟩
        · exact ⟨found, by simpa [lookupLeaf, ho] using hfound⟩

theorem lookupLeaf_some_iff (leaves : Leaves) (digest : Digest)
    (data : LeafData)
    (huniq : ∀ left right d, (left, d) ∈ leaves →
      (right, d) ∈ leaves → left = right) :
    lookupLeaf leaves digest = some data ↔ (data, digest) ∈ leaves := by
  constructor
  · exact lookupLeaf_mem
  · intro hmem
    obtain ⟨found, hfound⟩ := lookupLeaf_exists_mem hmem
    have hfoundMem := lookupLeaf_mem hfound
    have heq := huniq found data digest hfoundMem hmem
    cases heq
    exact hfound

theorem lookupLeaf_eq (leaves1 leaves2 : Leaves)
    (hmem : ∀ data digest, (data, digest) ∈ leaves1 ↔
      (data, digest) ∈ leaves2)
    (huniq : ∀ left right digest, (left, digest) ∈ leaves1 →
      (right, digest) ∈ leaves1 → left = right) :
    ∀ digest, lookupLeaf leaves1 digest = lookupLeaf leaves2 digest := by
  have huniq2 : ∀ left right digest, (left, digest) ∈ leaves2 →
      (right, digest) ∈ leaves2 → left = right := by
    intro left right digest hleft hright
    exact huniq left right digest (hmem left digest).2 hleft
      ((hmem right digest).2 hright)
  intro digest
  cases hleft : lookupLeaf leaves1 digest with
  | none =>
      cases hright : lookupLeaf leaves2 digest with
      | none => rfl
      | some data2 =>
          have hmem2 :=
            (lookupLeaf_some_iff leaves2 digest data2 huniq2).mp hright
          have hmem1 := (hmem data2 digest).mpr hmem2
          have hsome :=
            (lookupLeaf_some_iff leaves1 digest data2 huniq).mpr hmem1
          rw [hleft] at hsome
          cases hsome
  | some data1 =>
      have hmem1 :=
        (lookupLeaf_some_iff leaves1 digest data1 huniq).mp hleft
      have hmem2 := (hmem data1 digest).mp hmem1
      exact (lookupLeaf_some_iff leaves2 digest data1 huniq2).mpr hmem2

#print axioms lookupLeaf_some_iff
#print axioms lookupLeaf_eq

end AspisR1.MerkleLeafLookupExt
