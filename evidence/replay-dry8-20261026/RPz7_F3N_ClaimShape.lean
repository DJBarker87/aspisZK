import RPz7_F3M_ClaimNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_ClaimShape
open scoped BigOperators
attribute [local irreducible] HAdd.hAdd HMul.hMul HPow.hPow Finset.sum

theorem value (Y : Fin 6 → Fin 29 → AspisWideTower.WideExact)
    (c0 gamma kappa : AspisWideTower.WideExact) :
    c0+(∑ j : Fin 6,kappa^(j.val+1)*(∑ l : Fin 29,gamma^l.val*Y j l))=
      JointFunctionalBinding.claimedValue Y c0 gamma kappa := by
  unfold JointFunctionalBinding.claimedValue
  rfl

#print axioms value
end AspisR1.F3N_ClaimShape
end
