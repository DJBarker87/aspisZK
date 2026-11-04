import NGH_AccumulateRef
set_option autoImplicit false
namespace NGH_CellComposition
open Aeneas Aeneas.Std Result NGA_Cell

/-- Selected-cell equality and the complement frame refer to the same output. -/
theorem one_eq (s out : Sums) (l r : Cache) (c : Cell)
 (hl : (get l c).val < 2147483647) (hr : (get r c).val < 2147483647)
 (hs : (get s c).val ≤ 3*(2147483647-1)^2)
 (selected : (get out c).val = (get s c).val + (get l c).val*(get r c).val)
 (frame : ∀ d, d ≠ c → get out d = get s d) :
 NGA_Cell.step s l r (uFin c.1) (uFin c.2) = ok out := by
 obtain ⟨expected, run, values⟩ := NGA_Step.source s l r c hl hr hs
 have eq : expected = out := by
   apply NGA_ArrayExt.source
   intro d
   rw [values d]
   by_cases h : d = c
   · subst d
     simpa using selected.symm
   · simp only [if_neg h, Nat.add_zero]
     exact congrArg (fun v => v.val) (frame d h).symm
 simpa only [eq] using run

/-- The already checked nine-cell traversal is precisely the reference's loop. -/
theorem nine (s : Sums) (l r : Cache)
 (hl : NGA_CacheDomain.Bounded l) (hr : NGA_CacheDomain.Bounded r)
 (hs : ∀ c, (get s c).val ≤ 3*(2147483647-1)^2) :
 ∃ out, NGH_AccumulateRef.cells NGA_Nine.trace s l r = ok out ∧
 ∀ d, (get out d).val = (get s d).val + NGA_Nine.product l r d := by
 simpa only [NGH_AccumulateRef.cells_eq] using NGA_Nine.source s l r hl hr hs

#print axioms one_eq
#print axioms nine
end NGH_CellComposition
