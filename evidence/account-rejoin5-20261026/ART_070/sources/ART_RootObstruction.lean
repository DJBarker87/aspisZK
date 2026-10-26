import SCI_Recovery
set_option autoImplicit false
namespace AspisR1.ART_RootObstruction

/-- Rc10 quantifies runtime independently. Removing its binding without a
proved deployed-image representation permits this already checked runtime.
This is an interface countermodel, not an execution of the frozen program. -/
theorem independent :
    ¬ F3T_Runtime.deployedFailure SCI_Recovery.ObserverBoundary.runtime ≤ F3T_Numeric.total 0 := by
  rw [SCI_Recovery.ObserverBoundary.unrestricted_runtime]
  have small := F3T_Numeric.zero_queries
  have target : 1/(2:Rat)^100 < 1 := by norm_num
  exact not_le.mpr (small.trans target)

#print axioms independent
end AspisR1.ART_RootObstruction
