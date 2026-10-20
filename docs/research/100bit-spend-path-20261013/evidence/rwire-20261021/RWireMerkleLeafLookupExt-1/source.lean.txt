import BinMerkleRecordedLog

/-! Extensionality for recorded-leaf lookups. Membership equivalence and
per-digest uniqueness are explicit; no hash or recovery premise is used. -/
set_option autoImplicit false
namespace AspisR1.RWireMerkleLeafLookupExt

open AspisR1.BinMerkle32Path AspisR1.BinMerkleLeafRecovery
open AspisR1.BinMerkleRecordedLog

theorem lookupLeaf_some_iff (leaves : Leaves) (digest : Digest)
    (data : LeafData)
    (huniq : ∀ left right d, (left, d) ∈ leaves →
      (right, d) ∈ leaves → left = right) :
    lookupLeaf leaves digest = some data ↔ (data, digest) ∈ leaves := by
  constructor
  · exact lookupLeaf_mem
  · intro hmem
    obtain ⟨found, hfound⟩ := BinMerkleRecordedLog.lookupLeaf_exists hmem
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
    exact huniq left right digest ((hmem left digest).2 hleft)
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
      exact ((lookupLeaf_some_iff leaves2 digest data1 huniq2).mpr hmem2).symm

#print axioms lookupLeaf_some_iff
#print axioms lookupLeaf_eq


end AspisR1.RWireMerkleLeafLookupExt
