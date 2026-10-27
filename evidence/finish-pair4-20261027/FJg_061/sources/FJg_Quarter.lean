import FJg_ScalarValue
import FIp_CircleAlgebra
import R1RoundPairing
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_Quarter
open AspisR1CurrentWide.Proof

theorem base : decodeM FIo_Native.weights.QUARTER=R1ZCircleFoldMathV1.rustQuarter := rfl

theorem value (x : OraclePortCheckpointAbiC5.E) :
    decodeM FIo_Native.weights.QUARTER • x=RoundPairing.quarter*x := by
  rw [Algebra.smul_def,base,FIp_CircleAlgebra.quarter]
  rfl
#print axioms base
#print axioms value
end AspisR1.FJg_Quarter
end
