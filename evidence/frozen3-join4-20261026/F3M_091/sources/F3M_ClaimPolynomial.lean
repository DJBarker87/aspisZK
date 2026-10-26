import F3M_ModelClaimShape
import F3M_ClaimExpansion
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
  have initial := (F3M_ClaimTerms.zero kappa parts).trans zero
  have sum : (∑ j : Fin 6,kappaTerm kappa parts (j.val+1))=
      ∑ j : Fin 6,decode kappa^(j.val+1)*(∑ l : Fin 29,gamma^l.val*Y j l) := by
    apply Finset.sum_congr rfl
    intro j _
    exact (F3M_ClaimTerms.successor kappa parts j).trans
      (congrArg (fun x=>decode kappa^(j.val+1)*x) (rows j))
  have numeric := (F3M_ClaimExpansion.expansion kappa parts).trans
    (congrArg₂ (fun a b : AspisWideTower.WideExact=>a+b) initial sum)
  exact numeric.trans (F3M_ModelClaimShape.value (K:=AspisWideTower.WideExact) Y c0 gamma (decode kappa))

#print axioms polynomial
end AspisR1.F3M_ClaimPolynomial
end
