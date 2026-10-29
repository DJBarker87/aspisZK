import PV_B3P_PatternBinding12227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding12227
set_option autoImplicit false
/-- The complete existing source branch/inner-loop/outer-loop model, applied
to the unchanged per-function Link rather than left as an unused local law. -/
theorem pattern_link13 :
    PV_B3P_Links13227.PV_B3P_Link_copy_pattern_values_literal source_pattern_values12 :=
  funext (fun openings => funext (fun lambda => (pattern_values_literal_binding12 openings lambda).symm))
#print axioms pattern_link13
end PV_B3P_Binding13227
