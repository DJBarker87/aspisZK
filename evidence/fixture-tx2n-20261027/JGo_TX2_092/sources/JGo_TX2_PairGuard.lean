import JGo_TX2_NewWeights
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_PairGuard
open Aeneas Aeneas.Std Result

theorem same2 : JGo_TX2_WeightData.f02=JGo_TX2_WeightData.f22 := by rfl
#print axioms same2
theorem same3 : JGo_TX2_WeightData.f03=JGo_TX2_WeightData.f23 := by rfl
#print axioms same3

/-- Only the actual fixed-input branch selection, not Pair success. -/
theorem source : FIo_Native.weights.shared_two_point_guard
    (FIo_Install.toWeights JGo_TX2_WeightData.value) 2#usize=ok true := by
  with_unfolding_all rfl
#print axioms source
end AspisR1.JGo_TX2_PairGuard
end
