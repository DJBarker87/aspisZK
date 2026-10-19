import BinMerkleRecovery
import BinMerkle32Leaf

/-! Mirrors `MerkleLeafRecovery.lean`; see design/BIN-COMMITMENT-MODEL-20261019.md for line pins.
 A finite recorded-leaf lookup composed with the structural Merkle path
walk. The result is a deterministic disjunction; it makes no causal, source,
probability, or efficiency claim. -/
set_option autoImplicit false
namespace AspisR1.BinMerkleLeafRecovery

open AspisR1.BinMerkle32Path AspisR1.BinMerkle32Leaf
open AspisR1.BinMerkleTable AspisR1.BinMerkleRecovery

abbrev Byte := AspisR1.BinMerkle32Path.Byte
abbrev LeafData := List Byte × List Byte
abbrev Leaves := List (LeafData × Digest)

def lookupLeaf : Leaves → Digest → Option LeafData
  | [], _ => none
  | (data, recorded) :: rest, target =>
      if recorded = target then some data else lookupLeaf rest target

theorem lookupLeaf_mem {leaves : Leaves} {target : Digest} {data : LeafData}
    (h : lookupLeaf leaves target = some data) : (data, target) ∈ leaves := by
  induction leaves with
  | nil => simp [lookupLeaf] at h
  | cons entry rest ih =>
      rcases entry with ⟨recorded, digest⟩
      by_cases heq : digest = target
      · have hdata : recorded = data := by simpa [lookupLeaf, heq] using h
        subst recorded
        simp [heq]
      · have hrest : lookupLeaf rest target = some data := by
          simpa [lookupLeaf, heq] using h
        exact List.mem_cons_of_mem _ (ih hrest)

def leafInputs (tag : Byte) (leaves : Leaves) : List (List Byte) :=
  leaves.map fun entry => leafInput tag entry.1.1 entry.1.2

def LeafConsistent (hash : List Byte → Digest) (tag : Byte) (leaves : Leaves) : Prop :=
  ∀ data digest, (data, digest) ∈ leaves → hash (leafInput tag data.1 data.2) = digest

def Width (leaves : Leaves) (packedWidth : Nat) : Prop :=
  ∀ data digest, (data, digest) ∈ leaves → data.1.length = packedWidth

def recover (nodes : Nodes) (leaves : Leaves) (slots : List (Fin 2))
    (root : Digest) : Option LeafData :=
  (walk nodes slots root).bind (lookupLeaf leaves)

theorem recover_or_bad (hash : List Byte → Digest) (nodes : Nodes) (leaves : Leaves)
    (tag : Byte) (packed salt : List Byte)
    (nodesConsistent : BinMerkleRecovery.Consistent hash nodes)
    (leavesConsistent : LeafConsistent hash tag leaves)
    (w : Nat) (leafWidth : Width leaves w)
    (packedWidth : packed.length = w) (leaf : List Byte)
    (leafEq : leaf = leafInput tag packed salt)
    {slots : List (Fin 2)} (path : Path slots)
    (root : Digest)
    (rootEq : root = foldPath hash path (hash leaf)) :
    recover nodes leaves slots root = some (packed, salt) ∨
      CrossTraceCollision hash
        (BinMerkleRecovery.nodeInputs nodes ++ leafInputs tag leaves)
        (fullTrace hash path leaf) ∨
      MissingHit hash nodes root (inputTrace hash path (hash leaf)) ∨
      (hash leaf ∈ targets nodes root ∧ lookupLeaf leaves (hash leaf) = none) := by
  classical
  have hcases := BinMerkleRecovery.recover_or_bad hash nodes nodesConsistent path (hash leaf)
  rw [← rootEq] at hcases
  rcases hcases with hwalk | hcollision | hmissing
  · unfold recover
    rw [hwalk]
    cases hlookup : lookupLeaf leaves (hash leaf) with
    | none =>
        exact Or.inr (Or.inr (Or.inr ⟨walk_mem_targets nodes slots root (hash leaf) hwalk,
          rfl⟩))
    | some data =>
        have hmem := lookupLeaf_mem hlookup
        have hhash := leavesConsistent data (hash leaf) hmem
        by_cases heq : leafInput tag data.1 data.2 = leaf
        · rw [leafEq] at heq
          have hwidth : data.1.length = packed.length :=
            (leafWidth data (hash leaf) hmem).trans packedWidth.symm
          have hinj := leafInput_fixedWidth_injective tag data.1 data.2 packed salt
            hwidth heq
          rcases hinj with ⟨rfl, rfl⟩
          left
          simpa [hlookup]
        · right
          left
          refine ⟨leafInput tag data.1 data.2, ?_, leaf, ?_, heq, ?_⟩
          · apply List.mem_append.mpr
            exact Or.inr (List.mem_map.mpr ⟨(data, hash leaf), hmem, rfl⟩)
          · simp [fullTrace]
          · exact hhash
  · right
    left
    rcases hcollision with ⟨leftInput, hleft, rightInput, hright, hneq, hhash⟩
    exact ⟨leftInput, List.mem_append.mpr (Or.inl hleft), rightInput,
      List.mem_cons_of_mem _ hright, hneq, hhash⟩
  · right
    right
    left
    exact hmissing


#print axioms lookupLeaf_mem
#print axioms recover_or_bad

end AspisR1.BinMerkleLeafRecovery
