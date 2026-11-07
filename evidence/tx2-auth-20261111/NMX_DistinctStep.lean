import NMX_DistinctValues
set_option autoImplicit false
namespace NMX_DistinctStep
open Aeneas Aeneas.Std Result AdapterRw NGL_DistinctInduction
theorem success {N : Usize} (a : Array Account N) (n : Nat) (i : Usize) :
 outer a (n+1) i = ok none ↔
 NGL_DistinctInduction.inner a i i.val 0#usize = ok none ∧
 outer a n (Usize.wrapping_add i 1#usize) = ok none := by
 rcases NMX_DistinctValues.inner_values a i i.val 0#usize with normal | rejected
 · simp [outer,normal]
 · simp [outer,rejected]
#print axioms success
end NMX_DistinctStep
