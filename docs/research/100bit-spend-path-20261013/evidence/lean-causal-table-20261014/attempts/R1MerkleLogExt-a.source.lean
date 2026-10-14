import R1MerkleNodeLookupExt
import R1MerkleNodeRecordUnique
import R1MerkleLeafLookupExt
import R1MerkleLeafRecordUnique
import R1MerkleRecordedLog

/-! Deterministic extensionality of recorded Merkle recovery under equivalent
log membership, with hash separation used only to establish per-digest
functionality in the first log. -/
set_option autoImplicit false
namespace AspisR1.MerkleLogExt

open AspisR1.Merkle32Path AspisR1.MerkleTable
open AspisR1.MerkleLeafRecovery AspisR1.MerkleRecordedLog

theorem nodes_mem_eq (log1 log2 : Log)
    (hmem : ∀ input digest, (input, digest) ∈ log1 ↔ (input, digest) ∈ log2) :
    ∀ cs digest, (cs, digest) ∈ nodes log1 ↔ (cs, digest) ∈ nodes log2 := by
  intro cs digest
  constructor
  · intro h
    obtain ⟨input, hentry, hparse⟩ := mem_nodes.mp h
    exact mem_nodes.mpr ⟨input, (hmem input digest).mp hentry, hparse⟩
  · intro h
    obtain ⟨input, hentry, hparse⟩ := mem_nodes.mp h
    exact mem_nodes.mpr ⟨input, (hmem input digest).mpr hentry, hparse⟩

theorem leaves_mem_eq (tag : Byte) (width : Nat) (log1 log2 : Log)
    (hmem : ∀ input digest, (input, digest) ∈ log1 ↔ (input, digest) ∈ log2) :
    ∀ data digest, (data, digest) ∈ leaves tag width log1 ↔
      (data, digest) ∈ leaves tag width log2 := by
  intro data digest
  constructor
  · intro h
    obtain ⟨input, hentry, hparse⟩ := mem_leaves.mp h
    exact mem_leaves.mpr ⟨input, (hmem input digest).mp hentry, hparse⟩
  · intro h
    obtain ⟨input, hentry, hparse⟩ := mem_leaves.mp h
    exact mem_leaves.mpr ⟨input, (hmem input digest).mpr hentry, hparse⟩

theorem recover_eq (hash : List Byte → Digest) (log1 log2 : Log)
    (hlog1 : Consistent hash log1)
    (hsep1 : ∀ a b da db, (a, da) ∈ log1 → (b, db) ∈ log1 →
      hash a = hash b → a = b)
    (hmem : ∀ input digest, (input, digest) ∈ log1 ↔ (input, digest) ∈ log2)
    (tag : Byte) (width : Nat) (slots : List (Fin 8)) (root : Digest) :
    MerkleLeafRecovery.recover (nodes log1) (leaves tag width log1) slots root =
      MerkleLeafRecovery.recover (nodes log2) (leaves tag width log2) slots root := by
  have hnodes := nodes_mem_eq log1 log2 hmem
  have hleaves := leaves_mem_eq tag width log1 log2 hmem
  have huniqNodes := MerkleNodeRecordUnique.nodes_unique_by_digest hash log1 hlog1 hsep1
  have huniqLeaves := MerkleLeafRecordUnique.leaves_digest_unique
    hash tag width log1 hlog1 hsep1
  have hwalk := MerkleNodeLookupExt.walk_eq (nodes log1) (nodes log2)
    hnodes huniqNodes slots root
  unfold MerkleLeafRecovery.recover
  rw [hwalk]
  cases hw : MerkleTable.walk (nodes log2) slots root with
  | none => rfl
  | some digest =>
      simpa [hw] using MerkleLeafLookupExt.lookupLeaf_eq
        (leaves tag width log1) (leaves tag width log2) hleaves huniqLeaves digest

#print axioms nodes_mem_eq
#print axioms leaves_mem_eq
#print axioms recover_eq

end AspisR1.MerkleLogExt
