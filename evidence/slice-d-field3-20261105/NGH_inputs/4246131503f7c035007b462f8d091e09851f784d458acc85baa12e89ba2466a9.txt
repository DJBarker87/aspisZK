import NGH_SmallRef
import NGA_OuterStep
set_option autoImplicit false
namespace NGH_OuterRef
open Aeneas Aeneas.Std Result NGA_Cell

/-- Same arrays, selected index, arbitrary pre-state and complete child reply. -/
theorem step_eq {n : Usize} (left right : Array NGA_Cache.Q n)
 (s : Sums) (index : Usize) :
 NGA_OuterStep.G left right s index NGH_AccumulateRef.run =
 NGA_OuterStep.G left right s index NGA_Accumulate.sourceModel := by
 simp only [NGA_OuterStep.G, NGH_AccumulateRef.model_eq]

/-- Every native outer-step domain is discharged on the actual selected pair. -/
theorem source {n : Usize} (left right : Array NGA_Cache.Q n)
 (s : Sums) (index : Usize) (arity : n.val ≤ 4) (active : index.val < n.val)
 (hl : ∀ x ∈ left.val, NGA_Cache.Canonical x)
 (hr : ∀ x ∈ right.val, NGA_Cache.Canonical x)
 (budget : ∀ d, (get s d).val ≤ 3*(2147483647-1)^2) :
 ∃ l r out next,
 Array.index_usize left index = ok l ∧ Array.index_usize right index = ok r ∧
 NGA_Cache.Canonical l ∧ NGA_Cache.Canonical r ∧
 NGH_AccumulateRef.run s l r = ok out ∧ next.val = index.val+1 ∧
 NGA_OuterStep.G left right s index NGH_AccumulateRef.run = ok (out,next) := by
 simpa only [NGH_AccumulateRef.model_eq, step_eq] using
   NGA_OuterStep.source left right s index arity active hl hr budget

#print axioms step_eq
#print axioms source
end NGH_OuterRef
