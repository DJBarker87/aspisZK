import PV_B3P_ArrayInterface543227
import PV_B3P_NativeActive15227
import PV_B3P_NativePattern15227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Association546227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Links13227 PV_B3P_Native15227
set_option autoImplicit false

/-- Local literal-body links; cfg reachability and optimized dispatch are
recorded separately. These equalities do not substitute the optimized body. -/
theorem active_literal_source_link546 : PV_B3P_Link_copy_active_literal native_active15 :=
  funext native_active_binding15

theorem pattern_literal_source_link546 : PV_B3P_Link_copy_pattern_values_literal native_pattern15 :=
  funext fun openings => funext fun lambda => native_pattern_binding15 openings lambda

#print axioms active_literal_source_link546
#print axioms pattern_literal_source_link546
end PV_B3P_Association546227
