import F3M_ModelClaimShape
import RPz7_F3M_ClaimExpansion
import RPz7_F3M_ClaimTerms
import F3M_SevenTerms
import OraclePortAcceptedContextC6
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_ClaimNumeric
open Aeneas Aeneas.Std
open AspisR1CurrentPreparedClaim.Concrete AspisR1CurrentPreparedClaim.ClaimParts
open scoped BigOperators

theorem numeric (kappa : E) (parts : Array E 7#usize)
    (Y : Fin 6 → Fin 29 → AspisWideTower.WideExact) (c0 gamma : AspisWideTower.WideExact)
    (zero : decode (parts.val[0]'(by have h : parts.val.length=7:=parts.property;omega))=c0)
    (rows : ∀ j : Fin 6,decode (parts.val[j.val+1]'(by have h : parts.val.length=7:=parts.property;omega))=
      ∑ l : Fin 29,gamma^l.val * Y j l) :
    kappaPolynomial kappa parts=c0+
      ∑ j : Fin 6,decode kappa^(j.val+1)*(∑ l : Fin 29,gamma^l.val*Y j l) := by
  have initial := (F3M_ClaimTerms.zero kappa parts).trans zero
  have sum : (∑ j : Fin 6,kappaTerm kappa parts (j.val+1))=
      ∑ j : Fin 6,decode kappa^(j.val+1)*(∑ l : Fin 29,gamma^l.val*Y j l) := by
    apply Finset.sum_congr rfl
    intro j _
    exact (F3M_ClaimTerms.successor kappa parts j).trans
      (congrArg (fun x=>decode kappa^(j.val+1)*x) (rows j))
  have numeric := (F3M_ClaimExpansion.expansion kappa parts).trans
    (congrArg₂ (fun a b : AspisWideTower.WideExact=>a+b) initial sum)
  exact numeric

#print axioms numeric
end AspisR1.F3M_ClaimNumeric
end
