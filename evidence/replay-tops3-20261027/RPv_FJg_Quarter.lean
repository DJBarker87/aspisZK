import RPv_FJg_QuarterBase
import SAG_QuarterTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_Quarter
open AspisR1CurrentWide.Proof
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (x : OraclePortCheckpointAbiC5.E) :
    decodeM FIo_Native.weights.QUARTER • x=RoundPairing.quarter*x := by
  have h := SAG_QuarterTransport.value (algebraMap ExactM OraclePortCheckpointAbiC5.E)
    (decodeM FIo_Native.weights.QUARTER) FJg_QuarterBase.value
  rw [Algebra.smul_def,h]
  rfl
#print axioms value
end AspisR1.FJg_Quarter
end
