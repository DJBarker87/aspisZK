import FJg_QuarterHorner
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_LowTransport
open scoped BigOperators

def horner {R : Type} [CommRing R] (f : Fin 4 → R) (a : R) : R :=
  f 0+a*(f 3+a*(f 2+a*f 1))

theorem sum {R : Type} [CommRing R] (f : Fin 4 → R) (a : R) :
    (∑ s : Fin 4,f s*a^((4-s.val)%4))=horner f a := by
  rw [Fin.sum_univ_four]
  change f 0*a^0+f 1*a^3+f 2*a^2+f 3*a^1=_
  unfold horner
  simp only [pow_zero,pow_succ,mul_one]
  ring

attribute [local irreducible] QuadraticAlgebra.instInv RoundPairing.quarter FJg_DualTensor.low
abbrev FE := OraclePortCheckpointAbiC5.E

theorem value (f : Fin 4 → FE) (a : FE) :
    AspisR1CurrentWide.Proof.decodeM FIo_Native.weights.QUARTER •
      (∑ s : Fin 4,f s*a^((4-s.val)%4))=FJg_DualTensor.low f a := by
  rw [sum]
  have same : horner f a=FJg_LowHorner.horner f a := rfl
  rw [same]
  exact FJg_QuarterHorner.value f a
#print axioms sum
#print axioms value
end AspisR1.FJg_LowTransport
end
