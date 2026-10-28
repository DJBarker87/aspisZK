import PV_L2D_MerkleSafe
set_option autoImplicit false
namespace PV_L2D_TreeShape
open PV_L2D_MerklePlan

def parentCells (hash : Digest → Digest → Digest) : List Digest → List Digest
  | [] => []
  | [_] => []
  | a::b::xs => hash a b :: parentCells hash xs

theorem parent_length (hash : Digest → Digest → Digest) (xs : List Digest) :
    (parentCells hash xs).length=xs.length/2 := by
  fun_induction parentCells hash xs <;> simp_all [parentCells] <;> omega
#print axioms parent_length

def tree (hash : Digest → Digest → Digest) : Nat → List Digest → List (List Digest)
  | 0, leaves => [leaves]
  | n+1, leaves => leaves::tree hash n (parentCells hash leaves)

theorem level_count (hash : Digest → Digest → Digest) (n : Nat) (leaves : List Digest) :
    (tree hash n leaves).length=n+1 := by
  induction n generalizing leaves with
  | zero => rfl
  | succ n ih => simp [tree,ih]
#print axioms level_count

theorem level_shape (hash : Digest → Digest → Digest) (n j : Nat) (leaves : List Digest)
    (hlen : leaves.length=2^n) (hj : j≤n) :
    ∃ cells, (tree hash n leaves)[j]?=some cells ∧ cells.length=2^(n-j) := by
  induction n generalizing j leaves with
  | zero =>
    have hj0 : j=0 := by omega
    subst j
    exact ⟨leaves,rfl,hlen⟩
  | succ n ih =>
    cases j with
    | zero => exact ⟨leaves,rfl,by simpa using hlen⟩
    | succ j =>
      have hp : (parentCells hash leaves).length=2^n := by
        rw [parent_length,hlen,pow_succ]
        omega
      obtain ⟨cells,hc,hs⟩ := ih j (parentCells hash leaves) hp (by omega)
      exact ⟨cells,by simpa [tree] using hc,by simpa using hs⟩
#print axioms level_shape

theorem root_exists (hash : Digest → Digest → Digest) (n : Nat) (leaves : List Digest)
    (hlen : leaves.length=2^n) :
    ∃ cells, (tree hash n leaves)[n]?=some cells ∧ cells.length=1 := by
  obtain ⟨cells,hc,hs⟩ := level_shape hash n n leaves hlen (by rfl)
  exact ⟨cells,hc,by simpa using hs⟩
#print axioms root_exists

/-- Every planned callback has an in-range node index in the constructed
symbolic tree, for every hash value function and every leaf payload. -/
theorem planned_read (hash : Digest → Digest → Digest) (leaves : List Digest)
    (hlen : leaves.length=2^18) (xs : List Nat) (domain : ∀ x∈xs,x<2^18)
    (a : Address) (ha : a∈plan 18 0 xs) :
    ∃ cells, (tree hash 18 leaves)[a.1]?=some cells ∧ a.2<cells.length := by
  obtain ⟨hd,hi⟩ := PV_L2D_MerkleSafe.eighteen xs domain a ha
  obtain ⟨cells,hc,hs⟩ := level_shape hash 18 a.1 leaves hlen (by omega)
  exact ⟨cells,hc,by omega⟩
#print axioms planned_read
end PV_L2D_TreeShape
