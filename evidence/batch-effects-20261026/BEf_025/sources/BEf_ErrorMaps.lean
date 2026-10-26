import Op5T_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEf_ErrorMaps
open Aeneas Aeneas.Std Result

/-- TX1's actual installed error map does not repair the rejected-tail
outer-panic versus inner-Parse distinction. -/
theorem current :
    Op5T_Install.mapResult Op5T_Install.currentError
      (.fail .panic : Result (core.result.Result Unit AspisR1Stage2.verifier.Error)) ≠
      .ok (.Err AspisR1CurrentCaller.verifier.Error.Parse) := by
  intro same
  cases same

/-- The same obstruction remains at TX2's distinct nominal Error type. -/
theorem stage :
    Op5T_Install.mapResult Op5T_Install.stageError
      (.fail .panic : Result (core.result.Result Unit AspisR1Stage2.verifier.Error)) ≠
      .ok (.Err (Op5T_Install.stageError AspisR1Stage2.verifier.Error.Parse)) := by
  intro same
  cases same

#print axioms current
#print axioms stage
end AspisR1.BEf_ErrorMaps
end
