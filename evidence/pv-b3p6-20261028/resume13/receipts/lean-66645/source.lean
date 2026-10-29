import PV_B3P_LinkDefinitions13227
import PV_B3P_InternalBinding12227
import PV_B3P_Operations12227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Links13227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding12227
set_option autoImplicit false
theorem internal_link13 : PV_B3P_Link_poseidon_internal_linear_lazy (source_internal12) :=
  funext fun state => (internal_linear_binding12 state).symm
#print axioms internal_link13
end PV_B3P_Binding13227
