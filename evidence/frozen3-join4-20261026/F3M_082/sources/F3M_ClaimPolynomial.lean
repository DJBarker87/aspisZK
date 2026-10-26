import F3M_ClaimTerms
import F3M_SevenTerms
import OraclePortAcceptedContextC6
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_ClaimPolynomial
open Aeneas Aeneas.Std
open AspisR1CurrentPreparedClaim.Concrete AspisR1CurrentPreparedClaim.ClaimParts
open scoped BigOperators

theorem polynomial (kappa : E) (parts : Array E 7#usize)
    (Y : Fin 6 → Fin 29 → AspisWideTower.WideExact) (c0 gamma : AspisWideTower.WideExact)
    (zero : decode (parts.val[0]'(by have h : parts.val.length=7:=parts.property;omega))=c0)
    (rows : ∀ j : Fin 6,decode (parts.val[j.val+1]'(by have h : parts.val.length=7:=parts.property;omega))=
      ∑ l : Fin 29,gamma^l.val * Y j l) :
    kappaPolynomial kappa parts=JointFunctionalBinding.claimedValue Y c0 gamma (decode kappa) := by
  rw [kappaPolynomial,F3M_SevenTerms.split,F3M_ClaimTerms.zero,zero]
  unfold JointFunctionalBinding.claimedValue
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [F3M_ClaimTerms.successor,rows]

#print axioms polynomial
end AspisR1.F3M_ClaimPolynomial
end
