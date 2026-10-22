import R1Z.BatchedAlgebra
/-! Symbolic dual Horner identity, before concrete quarter instantiation. -/
set_option autoImplicit false
namespace R1Z.ProverCommitDualMath49
open scoped BigOperators
variable {K : Type} [Field K]

theorem horner_model (q : Nat → K) (a : K) (i : Fin 256) :
    (q (4*i.val)+a*q (4*i.val+3)+a^2*q (4*i.val+2)+a^3*q (4*i.val+1))*(4 : K)⁻¹=
      AspisR1.RoundPairing.dualFold a (fun j : Fin 1024 => q j.val) i := by
  simp only [AspisR1.RoundPairing.dualFold,AspisR1.RoundPairing.quarter,Fin.sum_univ_succ,
    Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ,add_zero]
  change (q (4*i.val)+a*q (4*i.val+3)+a^2*q (4*i.val+2)+a^3*q (4*i.val+1))*(4 : K)⁻¹=
    (4 : K)⁻¹*(q (4*i.val)*a^0+(q (4*i.val+1)*a^3+(q (4*i.val+2)*a^2+q (4*i.val+3)*a^1)))
  ring

#print axioms horner_model
end R1Z.ProverCommitDualMath49
