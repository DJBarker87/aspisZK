import RPu_FJj_HornerConcrete
import RPu_FJg_ScaleSum
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_LowSum
open scoped BigOperators

theorem horner {R : Type} [CommRing R] (f : Fin 4 → R) (a : R) :
    (∑ s : Fin 4,f s*a^((4-s.val)%4))=FJj_HornerInstances.horner f a := by
  rw [Fin.sum_univ_four]
  change f 0*a^0+f 1*a^3+f 2*a^2+f 3*a^1=_
  unfold FJj_HornerInstances.horner
  simp only [pow_zero,pow_succ,mul_one]
  ring

attribute [local irreducible] QuadraticAlgebra.instInv RoundPairing.quarter FJg_DualTensor.low
abbrev FE := OraclePortCheckpointAbiC5.E

theorem value (f : Fin 4 → FE) (a : FE) :
    AspisR1CurrentWide.Proof.decodeM FIo_Native.weights.QUARTER •
      (∑ s : Fin 4,f s*a^((4-s.val)%4))=FJg_DualTensor.low f a := by
  rw [horner,FJj_HornerConcrete.value]
  exact FJg_QuarterHorner.value f a
#print axioms horner
#print axioms value
end AspisR1.FJj_LowSum
end
