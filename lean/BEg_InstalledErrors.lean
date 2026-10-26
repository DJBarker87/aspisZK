import BEg_Observation
import Op5T_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEg_InstalledErrors
open Aeneas Aeneas.Std Result

theorem mapped {E : Type} (map : AspisR1Stage2.verifier.Error → E)
    (out : Result (core.result.Result Unit AspisR1Stage2.verifier.Error)) :
    BEg_Observation.accepted (Op5T_Install.mapResult map out) =
      BEg_Observation.accepted out := by
  cases out with
  | fail e => rfl
  | div => rfl
  | ok value => cases value <;> rfl

/-- Exact TX1 installed error map. -/
theorem current (out : Result (core.result.Result Unit AspisR1Stage2.verifier.Error)) :
    BEg_Observation.accepted (Op5T_Install.mapResult Op5T_Install.currentError out) =
      BEg_Observation.accepted out := mapped _ out

/-- Exact TX2 installed error map. -/
theorem stage (out : Result (core.result.Result Unit AspisR1Stage2.verifier.Error)) :
    BEg_Observation.accepted (Op5T_Install.mapResult Op5T_Install.stageError out) =
      BEg_Observation.accepted out := mapped _ out

#print axioms mapped
#print axioms current
#print axioms stage
end AspisR1.BEg_InstalledErrors
end
