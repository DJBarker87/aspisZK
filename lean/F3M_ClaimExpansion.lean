import F3M_ClaimTerms
import F3M_SevenTerms
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_ClaimExpansion
open Aeneas Aeneas.Std
open AspisR1CurrentPreparedClaim.Concrete AspisR1CurrentPreparedClaim.ClaimParts
open scoped BigOperators

theorem expansion (kappa : E) (parts : Array E 7#usize) :
    kappaPolynomial kappa parts=kappaTerm kappa parts 0+
      ∑ j : Fin 6,kappaTerm kappa parts (j.val+1) :=
  F3M_SevenTerms.split (kappaTerm kappa parts)

#print axioms expansion
end AspisR1.F3M_ClaimExpansion
end
