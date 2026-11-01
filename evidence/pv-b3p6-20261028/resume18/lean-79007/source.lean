import PV_B3P_ArrayInterface543227
import PV_B3P_EqualityNative14227
import PV_B3P_NativeOccupancy15227
import PV_B3P_InterpolationSource15227
import PV_B3P_PoseidonSelectorCaller15227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Association543227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Links13227
set_option autoImplicit false

/-- Source dossiers are external structural evidence. These lemmas state the
exact complete-Result equalities used there; they add no native-source axiom. -/
theorem equality_source_link543 :
    PV_B3P_Link_terminal_equality_value PV_B3P_Binding9227.source_equality_value :=
  funext fun left => funext fun right => PV_B3P_Binding9227.equality_body_binding left right

theorem occupancy_source_link543 :
    PV_B3P_Link_terminal_occupancy_lanes_literal PV_B3P_Native15227.native_occupancy15 :=
  funext fun input => funext fun output => funext fun expected => funext fun opened =>
    PV_B3P_Native15227.native_occupancy_binding15 input output expected opened

theorem poseidon_selectors_source_link543 :
    PV_B3P_Link_terminal_poseidon_selectors PV_B3P_Native15227.native_poseidon_selectors15 :=
  funext PV_B3P_Native15227.native_poseidon_selectors_binding15

theorem interpolation_source_link543 :
    PV_B3P_Link_poseidon_interpolate_three_constant_columns PV_B3P_Native15227.interpolation_source15 :=
  funext fun weights => funext fun first => funext fun second => funext fun third =>
    PV_B3P_Native15227.interpolation_source_binding15 weights first second third

#print axioms equality_source_link543
#print axioms occupancy_source_link543
#print axioms poseidon_selectors_source_link543
#print axioms interpolation_source_link543
end PV_B3P_Association543227
