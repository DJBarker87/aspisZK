import RPu_FJg_Quarter
import RPu_FJg_LowHorner
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_QuarterHorner
open AspisR1CurrentWide.Proof
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv RoundPairing.quarter FJg_LowHorner.horner

theorem value (f : Fin 4 → FE) (a : FE) :
    decodeM FIo_Native.weights.QUARTER • FJg_LowHorner.horner f a=
      FJg_DualTensor.low f a := by
  rw [FJg_LowHorner.value]
  exact FJg_Quarter.value _
#print axioms value
end AspisR1.FJg_QuarterHorner
end
