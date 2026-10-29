import PV_B3P_SelectorCorrection14227
import PV_B3P_SumHighLink13227
namespace PV_B3P_Correct14227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding13227
set_option autoImplicit false
/-- The actual local terminal constructor selects [0..57], independently of
point values. The same-name 49-block constructor is a distinct definition. -/
def selected_blocks14 : Usize := 57#usize

theorem actual_constructor_layout14 : PV_B3P_Link_constructor_call_layout selected_blocks14 := rfl

def selected_constructor14 : SelectorFn := constructor14 selected_blocks14

theorem selected_constructor_link14 :
    PV_B3P_Links13227.PV_B3P_Link_poseidon_at_point selected_constructor14 :=
  constructor_at_call14 selected_constructor14 constructor14 selected_blocks14
    constructor_on_layout14 actual_constructor_layout14 rfl

/-- A separate native association is still needed for the source Selectors
expansion and source sum iterator; choosing 57 alone does not prove either. -/
theorem selected_constructor_native_transport14 (native : SelectorFn)
    (association : PV_B3P_Link_constructor_native native constructor14 selected_blocks14) :
    PV_B3P_Links13227.PV_B3P_Link_poseidon_at_point native :=
  constructor_at_call14 native constructor14 selected_blocks14
    constructor_on_layout14 actual_constructor_layout14 association
#print axioms actual_constructor_layout14
#print axioms selected_constructor_link14
#print axioms selected_constructor_native_transport14
end PV_B3P_Correct14227
