import Mathlib.Tactic.FinCases
import R1Z.PV_Src_PortTables
import R1Z.PV_Src_PortSboxStep

set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalConstants
open Aeneas Aeneas.Std
open BuilderForestAdmissionPort

theorem canonical (r : Fin 14) : poseidon2.INTERNAL.val[r.val]!.val < 2147483647 := by
  fin_cases r <;> decide

#print axioms canonical
end R1Z.PV_Src_PortInternalConstants
