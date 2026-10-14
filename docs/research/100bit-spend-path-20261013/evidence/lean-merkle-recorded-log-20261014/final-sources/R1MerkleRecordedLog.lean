import R1MerkleNodeCodec
import R1MerkleLeafCodec

/-! Construct node and fixed-width salted-leaf records from a finite byte
query log. Parser completeness turns a failed digest lookup into absence
of that correctly encoded input from the log. Causal ordering, distinct-read
budgets, and correspondence to Rust execution remain separate. -/
set_option autoImplicit false
namespace AspisR1.MerkleRecordedLog

open Merkle32Path MerkleTable MerkleLeafRecovery

abbrev Byte := Merkle32Path.Byte
abbrev Log := List (List Byte × Digest)

def Consistent (hash : List Byte → Digest) (log : Log) : Prop :=
  ∀ input digest, (input, digest) ∈ log → hash input = digest

def nodes (log : Log) : Nodes :=
  log.filterMap fun entry =>
    (MerkleNodeCodec.parse entry.1).map fun children => (children, entry.2)

def leaves (tag : Byte) (width : Nat) (log : Log) : Leaves :=
  log.filterMap fun entry =>
    (MerkleLeafCodec.parse tag width entry.1).map fun data => (data, entry.2)

theorem mem_nodes {log : Log} {children : Children} {digest : Digest} :
    (children, digest) ∈ nodes log ↔
      ∃ input, (input, digest) ∈ log ∧ MerkleNodeCodec.parse input = some children := by
  simp only [nodes, List.mem_filterMap]
  constructor
  · rintro ⟨⟨input, output⟩, hin, hparse⟩
    cases hp : MerkleNodeCodec.parse input with
    | none => simp [hp] at hparse
    | some cs =>
        simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hparse
        rcases hparse with ⟨rfl, rfl⟩
        exact ⟨input, hin, hp⟩
  · rintro ⟨input, hin, hp⟩
    exact ⟨(input, digest), hin, by simp [hp]⟩

theorem mem_leaves {tag : Byte} {width : Nat} {log : Log}
    {data : LeafData} {digest : Digest} :
    (data, digest) ∈ leaves tag width log ↔
      ∃ input, (input, digest) ∈ log ∧ MerkleLeafCodec.parse tag width input = some data := by
  simp only [leaves, List.mem_filterMap]
  constructor
  · rintro ⟨⟨input, output⟩, hin, hparse⟩
    cases hp : MerkleLeafCodec.parse tag width input with
    | none => simp [hp] at hparse
    | some record =>
        simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hparse
        rcases hparse with ⟨rfl, rfl⟩
        exact ⟨input, hin, hp⟩
  · rintro ⟨input, hin, hp⟩
    exact ⟨(input, digest), hin, by simp [hp]⟩

theorem nodes_consistent (hash : List Byte → Digest) (log : Log)
    (hlog : Consistent hash log) : MerkleRecovery.Consistent hash (nodes log) := by
  intro cs d hentry
  obtain ⟨input, hin, hp⟩ := mem_nodes.mp hentry
  rw [MerkleNodeCodec.parse_sound hp]
  exact hlog input d hin

theorem leaves_consistent (hash : List Byte → Digest) (tag : Byte) (width : Nat)
    (log : Log) (hlog : Consistent hash log) :
    LeafConsistent hash tag (leaves tag width log) := by
  intro data d hentry
  obtain ⟨input, hin, hp⟩ := mem_leaves.mp hentry
  rw [(MerkleLeafCodec.parse_sound tag width input data hp).2.2]
  exact hlog input d hin

theorem leaves_width (tag : Byte) (width : Nat) (log : Log) :
    Width (leaves tag width log) width := by
  intro data d hentry
  obtain ⟨input, _, hp⟩ := mem_leaves.mp hentry
  exact (MerkleLeafCodec.parse_sound tag width input data hp).1

theorem node_present {log : Log} {children : Children} {digest : Digest}
    (hin : (nodeInput children, digest) ∈ log) :
    ∃ cs, lookup (nodes log) digest = some cs := by
  apply lookup_exists
  exact mem_nodes.mpr ⟨nodeInput children, hin, MerkleNodeCodec.parse_nodeInput children⟩

theorem lookupLeaf_exists {records : Leaves} {data : LeafData} {digest : Digest}
    (hin : (data, digest) ∈ records) :
    ∃ found, lookupLeaf records digest = some found := by
  induction records with
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

theorem leaf_present {tag : Byte} {width : Nat} {log : Log}
    {packed salt : List Byte} {digest : Digest}
    (hw : packed.length = width) (hs : salt.length = 32)
    (hin : (Merkle32Leaf.leafInput tag packed salt, digest) ∈ log) :
    ∃ found, lookupLeaf (leaves tag width log) digest = some found := by
  apply lookupLeaf_exists
  apply mem_leaves.mpr
  exact ⟨Merkle32Leaf.leafInput tag packed salt, hin,
    MerkleLeafCodec.parse_leafInput tag packed salt width hw hs⟩

theorem missing_node_absent (hash : List Byte → Digest) (log : Log)
    (hlog : Consistent hash log) (children : Children)
    (hmissing : lookup (nodes log) (hash (nodeInput children)) = none) :
    nodeInput children ∉ log.map Prod.fst := by
  rintro hin
  obtain ⟨⟨input, digest⟩, hentry, heq⟩ := List.mem_map.mp hin
  dsimp at heq
  subst input
  have hd := hlog (nodeInput children) digest hentry
  obtain ⟨cs, hcs⟩ := node_present hentry
  rw [← hd, hmissing] at hcs
  cases hcs

theorem missing_leaf_absent (hash : List Byte → Digest) (tag : Byte) (width : Nat)
    (log : Log) (hlog : Consistent hash log) (packed salt : List Byte)
    (hw : packed.length = width) (hs : salt.length = 32)
    (hmissing : lookupLeaf (leaves tag width log)
      (hash (Merkle32Leaf.leafInput tag packed salt)) = none) :
    Merkle32Leaf.leafInput tag packed salt ∉ log.map Prod.fst := by
  rintro hin
  obtain ⟨⟨input, digest⟩, hentry, heq⟩ := List.mem_map.mp hin
  dsimp at heq
  subst input
  have hd := hlog _ digest hentry
  obtain ⟨found, hfound⟩ := leaf_present hw hs hentry
  rw [← hd, hmissing] at hfound
  cases hfound

#print axioms mem_nodes
#print axioms mem_leaves
#print axioms nodes_consistent
#print axioms leaves_consistent
#print axioms leaves_width
#print axioms node_present
#print axioms lookupLeaf_exists
#print axioms leaf_present
#print axioms missing_node_absent
#print axioms missing_leaf_absent

end AspisR1.MerkleRecordedLog
