import FJg_ScalarValue
import SAG_QuarterBase
import SAG_QuarterTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_Quarter
open AspisR1CurrentWide.Proof

theorem base : (4 : ExactM)*decodeM FIo_Native.weights.QUARTER=1 := by
  change (4 : ZMod 2147483647)*536870912=1
  exact SAG_QuarterBase.four_times

theorem value (x : OraclePortCheckpointAbiC5.E) :
    decodeM FIo_Native.weights.QUARTER • x=RoundPairing.quarter*x := by
  have h := SAG_QuarterTransport.value (algebraMap ExactM OraclePortCheckpointAbiC5.E)
    (decodeM FIo_Native.weights.QUARTER) base
  rw [Algebra.smul_def,h]
  rfl
#print axioms base
#print axioms value
end AspisR1.FJg_Quarter
end
