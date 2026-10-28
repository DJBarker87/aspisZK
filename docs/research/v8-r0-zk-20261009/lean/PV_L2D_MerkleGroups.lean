import PV_L2D_MerklePlan
set_option autoImplicit false
namespace PV_L2D_MerkleGroups
open PV_L2D_MerklePlan

/-- The host count_parent's division test and the emitter's two child tests
select exactly the same pair on strictly increasing admitted indices. -/
theorem paired_iff (x y : Nat) (ordered : x<y) :
    y/2=x/2 ↔ y=2*(x/2)+1 ∧ x%2=0 := by omega
#print axioms paired_iff

def countedLevel : Nat → List Nat → List Nat × List Nat
  | 0, _ => ([],[])
  | _+1, [] => ([],[])
  | n+1, x::xs =>
    if xs.head?.map (fun y => y/2) = some (x/2) then
      let r := countedLevel n xs.tail
      (x/2 :: r.1,r.2)
    else
      let r := countedLevel n xs
      (x/2 :: r.1,sibling x :: r.2)

theorem group_test (x : Nat) (xs : List Nat) (h : ∀ y ∈ xs, x<y) :
    (xs.head?.map (fun y => y/2) = some (x/2)) ↔
      (xs.head? = some (2*(x/2)+1) ∧ x%2=0) := by
  cases xs with
  | nil => simp
  | cons y ys =>
    have hy : x<y := h y (by simp)
    simpa using paired_iff x y hy
#print axioms group_test

theorem counted_equals_emitted (fuel : Nat) (indices : List Nat)
    (ordered : indices.Pairwise (· < ·)) :
    countedLevel fuel indices = level fuel indices := by
  induction fuel generalizing indices with
  | zero => rfl
  | succ n ih =>
    cases indices with
    | nil => rfl
    | cons x xs =>
      have ht : xs.Pairwise (· < ·) := (List.pairwise_cons.mp ordered).2
      have hh : ∀ y ∈ xs, x<y := (List.pairwise_cons.mp ordered).1
      by_cases hp : xs.head? = some (2*(x/2)+1) ∧ x%2=0
      · have hc := (group_test x xs hh).mpr hp
        rw [countedLevel,if_pos hc,level,if_pos hp]
        rw [ih xs.tail ht.tail]
      · have hc : xs.head?.map (fun y => y/2) ≠ some (x/2) := by
          intro hc
          exact hp ((group_test x xs hh).mp hc)
        rw [countedLevel,if_neg hc,level,if_neg hp]
        rw [ih xs ht]
#print axioms counted_equals_emitted

/-- All control inputs retained: count and every source-ordered read. There
is no premise about digest equality or success of a Merkle verification. -/
def countedPlan : Nat → Nat → List Nat → List Address
  | 0, _, _ => []
  | n+1, depth, indices =>
    let r := countedLevel indices.length indices
    r.2.map (fun child => (depth,child)) ++ countedPlan n (depth+1) r.1

-- Parent-order preservation and whole eighteen-level equality are separate
-- from this local grouping theorem; no native row closure claimed here.
end PV_L2D_MerkleGroups
