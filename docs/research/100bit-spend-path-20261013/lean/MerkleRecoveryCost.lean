import R1MerkleLeafRecovery

/-! Executable finite-log recovery with an explicit digest-comparison count.
The returned result refines the existing recovery functions exactly. This
does not count parsing, byte comparisons or codeword/list-decoding work. -/
set_option autoImplicit false
namespace AspisR1.MerkleRecoveryCost
open Merkle32Path MerkleTable MerkleLeafRecovery

def lookupCount : Nodes → Digest → Option Children × Nat
  | [], _ => (none, 0)
  | (cs, h) :: rest, d =>
      if h = d then (some cs, 1)
      else let r := lookupCount rest d; (r.1, r.2 + 1)

theorem lookupCount_result (nodes : Nodes) (d : Digest) :
    (lookupCount nodes d).1 = MerkleTable.lookup nodes d := by
  induction nodes with
  | nil => rfl
  | cons q rest ih =>
      rcases q with ⟨cs, h⟩
      by_cases he : h = d <;> simp [lookupCount, MerkleTable.lookup, he, ih]

theorem lookupCount_cost (nodes : Nodes) (d : Digest) :
    (lookupCount nodes d).2 ≤ nodes.length := by
  induction nodes with
  | nil => simp [lookupCount]
  | cons q rest ih =>
      rcases q with ⟨cs, h⟩
      by_cases he : h = d
      · simp [lookupCount, he]
      · simpa [lookupCount, he] using Nat.add_le_add_right ih 1

def walkCount (nodes : Nodes) : List (Fin 8) → Digest → Option Digest × Nat
  | [], root => (some root, 0)
  | slot :: slots, root =>
      let r := walkCount nodes slots root
      match r.1 with
      | none => (none, r.2)
      | some parent =>
          let q := lookupCount nodes parent
          (q.1.map (fun cs => cs slot), r.2 + q.2)

theorem walkCount_result (nodes : Nodes) (slots : List (Fin 8)) (root : Digest) :
    (walkCount nodes slots root).1 = MerkleTable.walk nodes slots root := by
  induction slots generalizing root with
  | nil => rfl
  | cons slot slots ih =>
      simp only [walkCount, MerkleTable.walk]
      rw [← ih root]
      cases h : (walkCount nodes slots root).1 with
      | none => simp [h]
      | some parent => simp [h, lookupCount_result]

theorem walkCount_cost (nodes : Nodes) (slots : List (Fin 8)) (root : Digest) :
    (walkCount nodes slots root).2 ≤ slots.length * nodes.length := by
  induction slots generalizing root with
  | nil => simp [walkCount]
  | cons slot slots ih =>
      have hi := ih root
      have hq := fun parent => lookupCount_cost nodes parent
      simp only [walkCount, List.length_cons, Nat.add_mul, Nat.one_mul]
      cases h : (walkCount nodes slots root).1 with
      | none => simp only [h]; omega
      | some parent =>
          simp only [h]
          exact Nat.add_le_add hi (hq parent)

def lookupLeafCount : Leaves → Digest → Option LeafData × Nat
  | [], _ => (none, 0)
  | (data, h) :: rest, d =>
      if h = d then (some data, 1)
      else let r := lookupLeafCount rest d; (r.1, r.2 + 1)

theorem lookupLeafCount_result (leaves : Leaves) (d : Digest) :
    (lookupLeafCount leaves d).1 = MerkleLeafRecovery.lookupLeaf leaves d := by
  induction leaves with
  | nil => rfl
  | cons q rest ih =>
      rcases q with ⟨data, h⟩
      by_cases he : h = d <;> simp [lookupLeafCount, MerkleLeafRecovery.lookupLeaf, he, ih]

theorem lookupLeafCount_cost (leaves : Leaves) (d : Digest) :
    (lookupLeafCount leaves d).2 ≤ leaves.length := by
  induction leaves with
  | nil => simp [lookupLeafCount]
  | cons q rest ih =>
      rcases q with ⟨data, h⟩
      by_cases he : h = d
      · simp [lookupLeafCount, he]
      · simpa [lookupLeafCount, he] using Nat.add_le_add_right ih 1

def recoverCount (nodes : Nodes) (leaves : Leaves)
    (slots : List (Fin 8)) (root : Digest) : Option LeafData × Nat :=
  let r := walkCount nodes slots root
  match r.1 with
  | none => (none, r.2)
  | some d =>
      let q := lookupLeafCount leaves d
      (q.1, r.2 + q.2)

theorem recoverCount_result (nodes : Nodes) (leaves : Leaves)
    (slots : List (Fin 8)) (root : Digest) :
    (recoverCount nodes leaves slots root).1 =
      MerkleLeafRecovery.recover nodes leaves slots root := by
  simp only [recoverCount, MerkleLeafRecovery.recover, ← walkCount_result nodes slots root]
  cases h : (walkCount nodes slots root).1 with
  | none => simp [h]
  | some d => simp [h, lookupLeafCount_result]

theorem recoverCount_cost (nodes : Nodes) (leaves : Leaves)
    (slots : List (Fin 8)) (root : Digest) :
    (recoverCount nodes leaves slots root).2 ≤
      slots.length * nodes.length + leaves.length := by
  have hw := walkCount_cost nodes slots root
  simp only [recoverCount]
  cases h : (walkCount nodes slots root).1 with
  | none => simp only [h]; omega
  | some d =>
      simp only [h]
      exact Nat.add_le_add hw (lookupLeafCount_cost leaves d)

def recoverBatch (nodes : Nodes) (leaves : Leaves) (root : Digest) :
    List (List (Fin 8)) → List (Option LeafData) × Nat
  | [] => ([], 0)
  | slots :: rest =>
      let a := recoverCount nodes leaves slots root
      let b := recoverBatch nodes leaves root rest
      (a.1 :: b.1, a.2 + b.2)

theorem recoverBatch_result (nodes : Nodes) (leaves : Leaves) (root : Digest)
    (paths : List (List (Fin 8))) :
    (recoverBatch nodes leaves root paths).1 =
      paths.map (fun p => MerkleLeafRecovery.recover nodes leaves p root) := by
  induction paths with
  | nil => rfl
  | cons p ps ih => simp [recoverBatch, recoverCount_result, ih]

theorem recoverBatch_cost (nodes : Nodes) (leaves : Leaves) (root : Digest)
    (paths : List (List (Fin 8))) (depth : Nat)
    (hd : ∀ p ∈ paths, p.length ≤ depth) :
    (recoverBatch nodes leaves root paths).2 ≤
      paths.length * (depth * nodes.length + leaves.length) := by
  induction paths with
  | nil => simp [recoverBatch]
  | cons p ps ih =>
      have hp := (recoverCount_cost nodes leaves p root).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right nodes.length (hd p List.mem_cons_self)) _)
      have ht := ih (fun p h => hd p (List.mem_cons_of_mem _ h))
      simp only [recoverBatch, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- A conservative R1 three-word bound. Each word has at most 8^6 slots,
each path has at most six node lookups, and each filtered table has at most Q
records. Only digest-equality tests are counted. -/
theorem three_word_cost_le (nodes : Nodes) (leaves : Fin 3 → Leaves)
    (roots : Fin 3 → Digest) (paths : Fin 3 → List (List (Fin 8))) (Q : Nat)
    (hn : nodes.length ≤ Q) (hl : ∀ j, (leaves j).length ≤ Q)
    (hp : ∀ j, (paths j).length ≤ 262144)
    (hd : ∀ j p, p ∈ paths j → p.length ≤ 6) :
    (recoverBatch nodes (leaves 0) (roots 0) (paths 0)).2 +
      (recoverBatch nodes (leaves 1) (roots 1) (paths 1)).2 +
      (recoverBatch nodes (leaves 2) (roots 2) (paths 2)).2 ≤ 5505024 * Q := by
  have heach (j : Fin 3) :
      (recoverBatch nodes (leaves j) (roots j) (paths j)).2 ≤ 1835008 * Q := by
    have hbase := recoverBatch_cost nodes (leaves j) (roots j) (paths j) 6 (hd j)
    have hsize : 6 * nodes.length + (leaves j).length ≤ 7 * Q := by
      have h := hl j
      omega
    have hprod := Nat.mul_le_mul (hp j) hsize
    have hbound := hbase.trans hprod
    omega
  have h0 := heach 0
  have h1 := heach 1
  have h2 := heach 2
  omega

#print axioms lookupCount_result
#print axioms lookupCount_cost
#print axioms walkCount_result
#print axioms walkCount_cost
#print axioms lookupLeafCount_result
#print axioms lookupLeafCount_cost
#print axioms recoverCount_result
#print axioms recoverCount_cost
#print axioms recoverBatch_result
#print axioms recoverBatch_cost
#print axioms three_word_cost_le
end AspisR1.MerkleRecoveryCost
