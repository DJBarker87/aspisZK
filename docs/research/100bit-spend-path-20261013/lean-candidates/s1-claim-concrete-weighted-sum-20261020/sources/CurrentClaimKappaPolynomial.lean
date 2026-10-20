import CurrentClaimOuterSum
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.ClaimParts
open Concrete

def kappaTerm (kappa : E) (parts : Array E 7#usize) (j : Nat) : AspisWideTower.WideExact :=
  if h : j<7 then decode kappa^j * decode (parts.val[j]'(by rw [parts.property]; exact h)) else 0

def kappaPolynomial (kappa : E) (parts : Array E 7#usize) : AspisWideTower.WideExact :=
  ∑ j ∈ Finset.range 7, kappaTerm kappa parts j

theorem partialSum_is_kappa_polynomial (kappa : E) (k parts : Array E 7#usize)
    (hpowers : ∀ j : Fin 7, decode (k.val[j.val]'(by rw [k.property]; exact j.isLt))=decode kappa^j.val) :
    partialSum k parts 7=kappaPolynomial kappa parts := by
  unfold partialSum kappaPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  have hlt : j<7 := Finset.mem_range.mp hj
  simp only [term,kappaTerm,hlt,↓reduceDIte]
  rw [hpowers ⟨j,hlt⟩]

#print axioms partialSum_is_kappa_polynomial
end AspisR1CurrentPreparedClaim.ClaimParts
