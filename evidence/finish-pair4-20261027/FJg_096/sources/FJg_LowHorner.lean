import FJg_DualTensor
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_LowHorner
variable {E : Type} [Field E]

def horner (f : Fin 4 → E) (a : E) : E := f 0+a*(f 3+a*(f 2+a*f 1))

theorem value (f : Fin 4 → E) (a : E) :
    FJg_DualTensor.low f a=RoundPairing.quarter*horner f a := by
  unfold FJg_DualTensor.low
  rw [Fin.sum_univ_four]
  change RoundPairing.quarter*(f 0*a^0+f 1*a^3+f 2*a^2+f 3*a^1)=_
  unfold horner
  simp only [pow_zero,pow_one,pow_succ,mul_one]
  ring
#print axioms value
end AspisR1.FJg_LowHorner
end
