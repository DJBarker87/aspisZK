import BinTableWork

/-! Bounded byte comparisons and allocation during table lookup and path
walking. Equality is executed on 32-byte lists, rather than charged as an
unexplained constant on a function type. Failed walks retain their cost. -/
set_option autoImplicit false
namespace AspisR1.BinRecoveryWork
open BinMerkle32Path BinMerkleTable BinMerkleLeafRecovery

def digestEq (a b : Digest) : Bool × Nat :=
  let r := BinLeafListWork.equal (List.ofFn a) (List.ofFn b)
  (r.1, r.2 + 66)

theorem digestEq_value (a b : Digest) : (digestEq a b).1 = decide (a = b) := by
  simp only [digestEq, BinLeafListWork.equal_value, List.ofFn_inj]

theorem digestEq_work (a b : Digest) : (digestEq a b).2 ≤ 131 := by
  have h := BinLeafListWork.equal_work (List.ofFn a) (List.ofFn b)
  rw [List.length_ofFn] at h
  change _ + 66 ≤ _
  omega

def lookup {A : Type} : List (A × Digest) → Digest → Option A × Nat
  | [], _ => (none, 1)
  | (a, h) :: rest, d =>
    let eq := digestEq h d
    if eq.1 then (some a, eq.2 + 8)
    else let r := lookup rest d; (r.1, eq.2 + r.2 + 8)

theorem lookup_value {A : Type} (xs : List (A × Digest)) (d : Digest) :
    (lookup xs d).1 = (xs.find? (fun p => decide (p.2 = d))).map Prod.fst := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨a, h⟩
    by_cases he : h = d <;>
      simp only [lookup, digestEq_value, he, decide_true, decide_false,
        Bool.true_eq, if_true, if_false, List.find?_cons, Option.map_some, ih,
        Bool.false_eq_true, reduceCtorEq]

theorem lookup_work {A : Type} (xs : List (A × Digest)) (d : Digest) :
    (lookup xs d).2 ≤ 140 * xs.length + 1 := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons p xs ih =>
    rcases p with ⟨a, h⟩
    have he := digestEq_work h d
    simp only [lookup, List.length_cons]
    split <;> omega

theorem lookup_nodes (nodes : Nodes) (d : Digest) :
    (lookup nodes d).1 = BinMerkleTable.lookup nodes d := by
  induction nodes with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨a, h⟩
    by_cases he : h = d <;>
      simp only [lookup, BinMerkleTable.lookup, digestEq_value, he,
        decide_true, decide_false, Bool.true_eq, if_true, if_false, ih,
        Bool.false_eq_true, reduceCtorEq]

theorem lookup_leaves (leaves : Leaves) (d : Digest) :
    (lookup leaves d).1 = BinMerkleLeafRecovery.lookupLeaf leaves d := by
  induction leaves with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨a, h⟩
    by_cases he : h = d <;>
      simp only [lookup, BinMerkleLeafRecovery.lookupLeaf, digestEq_value, he,
        decide_true, decide_false, Bool.true_eq, if_true, if_false, ih,
        Bool.false_eq_true, reduceCtorEq]

def walk (nodes : Nodes) : List (Fin 2) → Digest → Option Digest × Nat
  | [], root => (some root, 1)
  | slot :: slots, root =>
    let r := walk nodes slots root
    match r.1 with
    | none => (none, r.2 + 4)
    | some parent =>
      let q := lookup nodes parent
      (q.1.map (fun cs => cs slot), r.2 + q.2 + 4)

theorem walk_value (nodes : Nodes) (slots : List (Fin 2)) (root : Digest) :
    (walk nodes slots root).1 = BinMerkleTable.walk nodes slots root := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    simp only [walk, BinMerkleTable.walk, ← ih]
    cases h : (walk nodes slots root).1 <;> simp only [h, lookup_nodes, Option.bind_none,
      Option.bind_some]

theorem walk_work (nodes : Nodes) (slots : List (Fin 2)) (root : Digest) :
    (walk nodes slots root).2 ≤ slots.length * (140 * nodes.length + 5) + 1 := by
  induction slots with
  | nil => simp only [walk, List.length_nil, Nat.zero_mul, Nat.zero_add, Nat.le_refl]
  | cons slot slots ih =>
    have hq := fun parent => lookup_work nodes parent
    simp only [walk, List.length_cons, Nat.add_mul, Nat.one_mul]
    cases h : (walk nodes slots root).1 with
    | none => simp only [h]; omega
    | some parent =>
      have hh := hq parent
      simp only [h]
      omega

def recover (nodes : Nodes) (leaves : Leaves) (slots : List (Fin 2))
    (root : Digest) : Option LeafData × Nat :=
  let r := walk nodes slots root
  match r.1 with
  | none => (none, r.2 + 4)
  | some d => let q := lookup leaves d; (q.1, r.2 + q.2 + 4)

theorem recover_value (nodes : Nodes) (leaves : Leaves) (slots : List (Fin 2))
    (root : Digest) : (recover nodes leaves slots root).1 =
      BinMerkleLeafRecovery.recover nodes leaves slots root := by
  simp only [recover, BinMerkleLeafRecovery.recover, ← walk_value nodes slots root]
  cases h : (walk nodes slots root).1 <;> simp only [h, lookup_leaves,
    Option.bind_none, Option.bind_some]

theorem recover_work (nodes : Nodes) (leaves : Leaves) (slots : List (Fin 2))
    (root : Digest) : (recover nodes leaves slots root).2 ≤
      slots.length * (140 * nodes.length + 5) + 140 * leaves.length + 6 := by
  have hw := walk_work nodes slots root
  simp only [recover]
  cases h : (walk nodes slots root).1 with
  | none => simp only [h]; omega
  | some d =>
    have hq := lookup_work leaves d
    simp only [h]
    omega

#print axioms digestEq_value
#print axioms digestEq_work
#print axioms lookup_value
#print axioms lookup_work
#print axioms lookup_nodes
#print axioms lookup_leaves
#print axioms walk_value
#print axioms walk_work
#print axioms recover_value
#print axioms recover_work
end AspisR1.BinRecoveryWork
