import Mathlib.Tactic.FinCases
import R1Z.PV_Src_PortTables
import R1Z.PV_Src_PortSboxStep

/-! Literal round constants are canonical. Only 64 scalar comparisons are
checked; no permutation or recurrence is evaluated. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortInitialConstants
open Aeneas Aeneas.Std
open BuilderForestAdmissionPort PV_Src_PortSboxStep

theorem canonical (r : Fin 4) : Canonical poseidon2.EXTERNAL_INITIAL.val[r.val]! := by
  intro j
  fin_cases r <;> fin_cases j <;> decide

#print axioms canonical
end R1Z.PV_Src_PortInitialConstants
