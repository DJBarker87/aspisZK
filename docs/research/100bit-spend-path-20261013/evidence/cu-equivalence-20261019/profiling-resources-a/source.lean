import CuSavingsProfilingProjection
/-! Resource admission for private byte-buffer diagnostic allocations.
For the pinned Solana bump allocator, align-one byte buffers subtract their
allocation sizes and deallocation is a no-op. `sizes` records actual allocator
requests, including reallocations; message length is not substituted for their
capacity. The callback source/SDK binding is recorded in the source audit. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsProfilingResources
open Aeneas Aeneas.Std Result

def privateAllocations : Nat → List Nat → Result Nat
  | free,[] => .ok free
  | free,size::sizes => if size ≤ free then privateAllocations (free-size) sizes else .fail .panic

/-- Numerical sufficient-reference-heap admission. Every allocation in the
actual private formatting trace succeeds, and the unchanged application keeps
its complete future reservation. -/
theorem private_allocations_admitted (sizes : List Nat) (free future : Nat)
    (budget : sizes.sum + future ≤ free) :
    privateAllocations free sizes = .ok (free-sizes.sum) ∧
      future ≤ free-sizes.sum := by
  induction sizes generalizing free with
  | nil => simp only [privateAllocations,List.sum_nil,Nat.sub_zero];exact ⟨rfl,budget⟩
  | cons size sizes ih =>
    have hsize : size ≤ free := by simp only [List.sum_cons] at budget;omega
    have hfuture : sizes.sum+future ≤ free-size := by simp only [List.sum_cons] at budget;omega
    obtain ⟨hrun,hremaining⟩ := ih (free-size) hfuture
    constructor
    · simp only [privateAllocations,hsize,if_pos,hrun,List.sum_cons]
      congr 1
      omega
    · simp only [List.sum_cons]
      omega

/-- Erasing private diagnostic allocations leaves at least the reference's
free heap and therefore retains every future reference allocation budget.
This conclusion does not equate two out-of-resources executions. -/
theorem erased_heap_dominates (sizes : List Nat) (free future : Nat)
    (budget : sizes.sum+future ≤ free) :
    future ≤ free-sizes.sum ∧ free-sizes.sum ≤ free ∧ future ≤ free := by
  have h := (private_allocations_admitted sizes free future budget).2
  exact ⟨h,Nat.sub_le _ _,by omega⟩

#print axioms private_allocations_admitted
#print axioms erased_heap_dominates
end AspisR1.CuSavingsProfilingResources
