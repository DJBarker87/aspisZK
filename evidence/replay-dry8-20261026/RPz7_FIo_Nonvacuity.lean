import RPz7_FIo_Install
import RPz7_FIn_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_Nonvacuity
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish

theorem arithmetic_fixed (r : AspisR1.NP6_StdModel.Reservation) (seed : FinishOps FIo_Install.W) :
    FIn_Install.finishOps (FIo_Install.finishOps r seed)=FIo_Install.finishOps r seed := rfl

/-- Successful installed Pair calls export an actual native successful result,
not an independently selected witness or an implication with a false guard. -/
theorem same_result (r : AspisR1.NP6_StdModel.Reservation) (seed : FinishOps FIo_Install.W)
    (w : FIo_Install.W) (alpha : Slice E) (f : Slice U8) (kappa out : E)
    (success : (FIo_Install.finishOps r seed).pair w alpha f kappa=ok (.Ok out)) :
    ∃ nativeOut, @FIo_Native.weights.Weights.pair (FIo_Install.allocation r)
      (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa)=ok (.Ok nativeOut) ∧
      FIo_Install.fromE nativeOut=out := FIo_Install.reached r w alpha f kappa out success

#print axioms arithmetic_fixed
#print axioms same_result
end AspisR1.FIo_Nonvacuity
end
