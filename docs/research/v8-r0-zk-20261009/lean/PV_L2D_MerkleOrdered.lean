import PV_L2D_MerkleGroups
set_option autoImplicit false
namespace PV_L2D_MerkleOrdered
open PV_L2D_MerklePlan PV_L2D_MerkleGroups

theorem tail_mem {x : Nat} {xs : List Nat} (h : x ∈ xs.tail) : x ∈ xs := by
  cases xs <;> simp_all
#print axioms tail_mem

theorem parent_mem (fuel : Nat) (xs : List Nat) (p : Nat)
    (h : p ∈ (level fuel xs).1) : ∃ x ∈ xs, p=x/2 := by
  induction fuel generalizing xs with
  | zero => simp [level] at h
  | succ n ih =>
    cases xs with
    | nil => simp [level] at h
    | cons x xs =>
      simp only [level] at h
      split at h
      · simp only [List.mem_cons] at h
        rcases h with he | ht
        · exact ⟨x,by simp,he⟩
        · obtain ⟨y,hy,he⟩ := ih xs.tail ht
          exact ⟨y,List.mem_cons_of_mem x (tail_mem hy),he⟩
      · simp only [List.mem_cons] at h
        rcases h with he | ht
        · exact ⟨x,by simp,he⟩
        · obtain ⟨y,hy,he⟩ := ih xs ht
          exact ⟨y,List.mem_cons_of_mem x hy,he⟩
#print axioms parent_mem

theorem no_pair_lower (x : Nat) (xs : List Nat)
    (ordered : (x::xs).Pairwise (· < ·))
    (unpaired : ¬(xs.head?=some (2*(x/2)+1) ∧ x%2=0)) :
    ∀ y ∈ xs, x/2 < y/2 := by
  cases xs with
  | nil => simp
  | cons y ys =>
    have hx := (List.pairwise_cons.mp ordered).1 y (by simp)
    have hne : y/2≠x/2 := by
      intro he
      have hp := (paired_iff x y hx).mp he
      exact unpaired (by simpa using hp)
    have hlt : x/2<y/2 := by omega
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hlt
    · have htail := (List.pairwise_cons.mp ordered).2
      have hy := (List.pairwise_cons.mp htail).1 z hz
      omega
#print axioms no_pair_lower

theorem ordered (fuel : Nat) (xs : List Nat)
    (h : xs.Pairwise (· < ·)) :
    ((level fuel xs).1).Pairwise (· < ·) := by
  induction fuel generalizing xs with
  | zero => simp [level]
  | succ n ih =>
    cases xs with
    | nil => simp [level]
    | cons x xs =>
      have ht := (List.pairwise_cons.mp h).2
      by_cases hp : xs.head?=some (2*(x/2)+1) ∧ x%2=0
      · rw [level,if_pos hp]
        apply List.pairwise_cons.mpr
        constructor
        · intro p hmem
          obtain ⟨z,hz,rfl⟩ := parent_mem n xs.tail p hmem
          cases xs with
          | nil => simp at hp
          | cons y ys =>
            have he : y=2*(x/2)+1 := by simpa using hp.1
            have hyz := (List.pairwise_cons.mp ht).1 z hz
            omega
        · exact ih xs.tail ht.tail
      · rw [level,if_neg hp]
        apply List.pairwise_cons.mpr
        constructor
        · intro p hmem
          obtain ⟨z,hz,rfl⟩ := parent_mem n xs p hmem
          exact no_pair_lower x xs h hp z hz
        · exact ih xs ht
#print axioms ordered

theorem counted_plan (levels depth : Nat) (xs : List Nat)
    (h : xs.Pairwise (· < ·)) : countedPlan levels depth xs = plan levels depth xs := by
  induction levels generalizing depth xs with
  | zero => rfl
  | succ n ih =>
    rw [countedPlan,plan,counted_equals_emitted xs.length xs h]
    rw [ih (depth+1) (level xs.length xs).1 (ordered xs.length xs h)]
#print axioms counted_plan
end PV_L2D_MerkleOrdered
