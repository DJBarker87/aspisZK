import OraclePortAcceptedContextC6
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_ModelClaimShape
open scoped BigOperators

theorem value {K : Type*} [Field K]
    (Y : Fin 6 → Fin 29 → K) (c0 gamma kappa : K) :
    c0+(∑ j : Fin 6,kappa^(j.val+1)*(∑ l : Fin 29,gamma^l.val*Y j l))=
      JointFunctionalBinding.claimedValue Y c0 gamma kappa := by
  rfl

#print axioms value
end AspisR1.F3M_ModelClaimShape
end
