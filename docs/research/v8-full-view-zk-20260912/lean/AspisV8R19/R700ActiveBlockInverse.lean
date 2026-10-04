import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R700ActiveBlockInverse
open scoped BigOperators
variable {I F : Type*} [Fintype I] [DecidableEq I] [CommRing F]
variable (block : I → Nat) (zero : I → Prop) [DecidablePred zero]

def blockRows (j : I) : Finset I := Finset.univ.filter (fun i => block i=block j)

def blockTransform (x : I → F) (j : I) : F :=
  if zero j then -(∑ i ∈ blockRows block j, x i) else x j

/-- A block's sole distinguished row is minus the block sum; the other
rows are retained. This transform is its own inverse. -/
theorem block_involution
    (unique : ∀ i j, zero i → zero j → block i=block j → i=j)
    (x : I → F) :
    blockTransform block zero (blockTransform block zero x)=x := by
  funext j
  by_cases hj : zero j
  · rw [blockTransform,if_pos hj]
    have hmem : j ∈ blockRows block j := by simp [blockRows]
    have hsum : (∑ i ∈ (blockRows block j).erase j, blockTransform block zero x i) =
        ∑ i ∈ (blockRows block j).erase j, x i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hne : i ≠ j := (Finset.mem_erase.mp hi).1
      have hb : block i=block j := (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).2
      have hzi : ¬zero i := fun hz => hne (unique i j hz hj hb)
      simp [blockTransform,hzi]
    rw [← Finset.sum_erase_add (blockRows block j) (blockTransform block zero x) hmem,hsum]
    rw [blockTransform,if_pos hj,← Finset.sum_erase_add (blockRows block j) x hmem]
    ring
  · simp [blockTransform,hj]

#print axioms block_involution
end AspisV8R19.R700ActiveBlockInverse
