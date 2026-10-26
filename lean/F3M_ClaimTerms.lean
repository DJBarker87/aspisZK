import F3M_PreparedClaim
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_ClaimTerms
open Aeneas Aeneas.Std
open AspisR1CurrentPreparedClaim.Concrete AspisR1CurrentPreparedClaim.ClaimParts

theorem zero (kappa : E) (parts : Array E 7#usize) :
    kappaTerm kappa parts 0=decode (parts.val[0]'(by have h : parts.val.length=7:=parts.property;omega)) := by
  simp only [kappaTerm,dif_pos (show (0 : Nat)<7 by decide),pow_zero,one_mul]

theorem successor (kappa : E) (parts : Array E 7#usize) (j : Fin 6) :
    kappaTerm kappa parts (j.val+1)=decode kappa^(j.val+1)*
      decode (parts.val[j.val+1]'(by have h : parts.val.length=7:=parts.property;omega)) := by
  simp only [kappaTerm,dif_pos (show j.val+1<7 by omega)]

#print axioms zero
#print axioms successor
end AspisR1.F3M_ClaimTerms
end
