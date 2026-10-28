import PV_L2D_MerkleOrdered
set_option autoImplicit false
namespace PV_L2D_MerkleGeometry
open PV_L2D_MerklePlan PV_L2D_MerkleOrdered

def parents (xs : List Nat) : List Nat := (level xs.length xs).1

def levels : Nat → List Nat → List Nat
  | 0, xs => xs
  | n+1, xs => parents (levels n xs)

theorem level_bound (fuel : Nat) (xs : List Nat) (b : Nat)
    (bound : ∀ x ∈ xs, x<2^b) :
    ∀ p ∈ (level fuel xs).1, p<2^(b-1) := by
  intro p hp
  obtain ⟨x,hx,rfl⟩ := parent_mem fuel xs p hp
  have h := bound x hx
  cases b with
  | zero => simp only [pow_zero] at h ⊢; omega
  | succ b =>
    simp only [Nat.add_sub_cancel,pow_succ] at h ⊢
    omega
#print axioms level_bound

theorem levels_bound (n b : Nat) (xs : List Nat)
    (bound : ∀ x ∈ xs, x<2^b) :
    ∀ x ∈ levels n xs, x<2^(b-n) := by
  induction n with
  | zero => simpa [levels] using bound
  | succ n ih =>
    have h := level_bound (levels n xs).length (levels n xs) (b-n) ih
    simpa only [levels,parents,show b-(n+1)=(b-n)-1 by omega] using h
#print axioms levels_bound

theorem levels_ordered (n : Nat) (xs : List Nat) (h : xs.Pairwise (· < ·)) :
    (levels n xs).Pairwise (· < ·) := by
  induction n with
  | zero => exact h
  | succ n ih => exact ordered _ _ ih
#print axioms levels_ordered

/-- A symbolic interval argument; no concrete Finset.univ/range of size 2^18. -/
theorem interval_count (xs : List Nat) (lo n : Nat)
    (ordered : xs.Pairwise (· < ·))
    (bound : ∀ x ∈ xs, lo≤x ∧ x<lo+n) : xs.length≤n := by
  induction xs generalizing lo n with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hlo,hhi⟩ := bound x (by simp)
    have ht := (List.pairwise_cons.mp ordered).2
    have hb : ∀ y ∈ xs, x+1≤y ∧ y<(x+1)+(lo+n-(x+1)) := by
      intro y hy
      have hyx := (List.pairwise_cons.mp ordered).1 y hy
      have hyy := bound y (List.mem_cons_of_mem x hy)
      omega
    have hi := ih (x+1) (lo+n-(x+1)) ht hb
    simp only [List.length_cons]
    omega
#print axioms interval_count

theorem occupancy_domain (j b : Nat) (xs : List Nat)
    (ordered : xs.Pairwise (· < ·)) (bound : ∀ x ∈ xs, x<2^b) :
    (levels j xs).length≤2^(b-j) := by
  exact interval_count (levels j xs) 0 (2^(b-j)) (levels_ordered j xs ordered)
    (by simpa using levels_bound j b xs bound)
#print axioms occupancy_domain

theorem occupancy_initial (j : Nat) (xs : List Nat) :
    (levels j xs).length≤xs.length := by
  induction j with
  | zero => rfl
  | succ j ih =>
    exact (level_parent_count _ _).trans ih
#print axioms occupancy_initial

theorem levels_shift (n : Nat) (xs : List Nat) :
    levels (n+1) xs = levels n (parents xs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change parents (levels (n+1) xs) = parents (levels n (parents xs))
    rw [ih]
#print axioms levels_shift
end PV_L2D_MerkleGeometry
