import RPv_FJg_Quarter
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_QuarterSquared
open AspisR1CurrentWide.Proof
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (x : OraclePortCheckpointAbiC5.E) :
    (decodeM FIo_Native.weights.QUARTER*decodeM FIo_Native.weights.QUARTER) • x=
      (RoundPairing.quarter*RoundPairing.quarter)*x := by
  rw [mul_smul,FJg_Quarter.value,FJg_Quarter.value]
  ring

#print axioms value
end AspisR1.FJr_QuarterSquared
end
