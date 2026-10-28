import PV_L2D_MerkleGeometry
import PV_L2D_SlotCaps
set_option autoImplicit false
namespace PV_L2D_MerkleCost
open PV_L2D_MerklePlan PV_L2D_MerkleGeometry

/-- Each admitted binary group consumes one or two occupied children;
all of its other children are exactly the emitted siblings. -/
theorem partition (fuel : Nat) (xs : List Nat) (enough : xs.length≤fuel) :
    (level fuel xs).2.length + xs.length = 2*(level fuel xs).1.length := by
  induction fuel generalizing xs with
  | zero =>
    have hx : xs=[] := by cases xs <;> simp_all
    simp [hx,level]
  | succ n ih =>
    cases xs with
    | nil => simp [level]
    | cons x xs =>
      simp only [level]
      split
      · rename_i hp
        have nonempty : xs≠[] := by intro he; simp [he] at hp
        have hlen : xs.length=xs.tail.length+1 := by cases xs <;> simp_all
        have ht := ih xs.tail (by simp only [List.length_cons] at enough; omega)
        simp only [List.length_cons]
        omega
      · have ht := ih xs (by simpa using Nat.le_of_succ_le_succ enough)
        simp only [List.length_cons]
        omega
#print axioms partition

def occupancy (xs : List Nat) (j : Nat) := (levels j xs).length

theorem binary_branch (xs : List Nat) (j : Nat) :
    occupancy xs j ≤ 2*occupancy xs (j+1) := by
  have h := partition (levels j xs).length (levels j xs) (by rfl)
  simp only [occupancy,levels,parents]
  omega
#print axioms binary_branch

theorem cost_step (xs : List Nat) (n : Nat) :
    PV_L2D_SlotCaps.missing (occupancy xs) (n+1) =
      (level xs.length xs).2.length + PV_L2D_SlotCaps.missing (occupancy (parents xs)) n := by
  have hp := partition xs.length xs (by rfl)
  have hd : 2*(parents xs).length-xs.length=(level xs.length xs).2.length := by
    dsimp only [parents]
    omega
  rw [PV_L2D_SlotCaps.missing,Finset.sum_range_succ']
  simp only [occupancy,levels_shift,levels]
  rw [hd]
  rw [Nat.add_comm]
  congr 1
  unfold PV_L2D_SlotCaps.missing occupancy
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← levels_shift (i+1) xs, ← levels_shift i xs]
  rfl
#print axioms cost_step

theorem plan_cost (n depth : Nat) (xs : List Nat) :
    (plan n depth xs).length = PV_L2D_SlotCaps.missing (occupancy xs) n := by
  induction n generalizing depth xs with
  | zero => simp [plan,PV_L2D_SlotCaps.missing]
  | succ n ih =>
    rw [plan,List.length_append,List.length_map]
    rw [ih,cost_step]
    rfl
#print axioms plan_cost

theorem ordinary_cap (xs : List Nat) (k depth : Nat)
    (size : xs.length≤k) (ordered : xs.Pairwise (· < ·))
    (domain : ∀ x ∈ xs, x<2^18) :
    (plan 18 depth xs).length≤13*k+16 := by
  rw [plan_cost]
  apply PV_L2D_SlotCaps.ordinary (occupancy xs) k size
    (fun i _hi => binary_branch xs i)
    (fun i _hi => occupancy_initial (i+1) xs)
  · exact occupancy_domain 15 18 xs ordered domain
  · exact occupancy_domain 16 18 xs ordered domain
  · exact occupancy_domain 17 18 xs ordered domain
  · exact occupancy_domain 18 18 xs ordered domain
#print axioms ordinary_cap

theorem folded_cap (xs : List Nat) (k depth : Nat)
    (size : xs.length≤k) (ordered : xs.Pairwise (· < ·))
    (domain : ∀ x ∈ xs, x<2^16) :
    (plan 18 depth xs).length≤11*k+18 := by
  rw [plan_cost]
  apply PV_L2D_SlotCaps.folded (occupancy xs) k size
    (fun i _hi => binary_branch xs i)
    (fun i _hi => occupancy_initial (i+1) xs)
  · exact occupancy_domain 13 16 xs ordered domain
  · exact occupancy_domain 14 16 xs ordered domain
  · exact occupancy_domain 15 16 xs ordered domain
  · exact occupancy_domain 16 16 xs ordered domain
  · exact occupancy_domain 17 16 xs ordered domain
  · exact occupancy_domain 18 16 xs ordered domain
#print axioms folded_cap
end PV_L2D_MerkleCost
