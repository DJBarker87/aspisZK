import NKB_CanonicalPair
set_option autoImplicit false
namespace NKB_CanonicalCongruence
open NKB_CanonicalPair

/-- Finite induction needs only reached windows, not a global oracle law or
accepted-run hypothesis. Useful for concrete decoder payload erasure. -/
theorem allFrom_congr (p q : Nat→Bool) (fuel start : Nat)
 (same : ∀ n,start≤n→n<start+fuel→p n=q n) :
 allFrom p start fuel=allFrom q start fuel := by
 induction fuel generalizing start with
 | zero=>rfl
 | succ fuel ih=>
   rw [allFrom,allFrom,same start (by omega) (by omega)]
   rw [ih (start+1) (by intro n lo hi;apply same n <;> omega)]

#print axioms allFrom_congr
end NKB_CanonicalCongruence
