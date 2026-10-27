import FJg_Quarter
import FJg_LowLane
import FJg_DualTensor
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_QuarterLow
open AspisR1CurrentWide.Proof
open scoped BigOperators
attribute [local irreducible] QuadraticAlgebra.instInv RoundPairing.quarter FJg_DualTensor.low
abbrev FE := OraclePortCheckpointAbiC5.E

theorem value (f : Fin 4 → FE) (a : FE) :
    decodeM FIo_Native.weights.QUARTER • (∑ s : Fin 4,f s*a^((4-s.val)%4))=
      FJg_DualTensor.low f a := by
  unfold FJg_DualTensor.low
  simp +singlePass +instances only [FJg_LowLane.semiring,FJg_LowLane.additive,FJg_LowLane.multiplicative]
  exact FJg_Quarter.value _
#print axioms value
end AspisR1.FJg_QuarterLow
end
