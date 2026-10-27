import PV_B1_Carrier230
import PV_B1_Carrier258
import PV_B1_CarrierWide
import PV_B1_Transport
set_option autoImplicit false
namespace PV_B1_CarrierContainers
open Aeneas Aeneas.Std PV_B1_Transport
abbrev HQ := PV_B1_Host.aspis_core.field.QM31
abbrev HW := PV_B1_Host.aspis_core.field.wide_exact.WideExact

theorem sum_input (xs : Slice HQ) :
    sliceMap PV_B1_Carrier230.fromQ (sliceMap PV_B1_Carrier230.toQ xs)=xs :=
  slice_roundtrip _ _ PV_B1_Carrier230.from_to xs

theorem powers_output (N : Usize) (xs : Array HW N) :
    arrayMap PV_B1_CarrierWide.fromW (arrayMap PV_B1_CarrierWide.toW xs)=xs :=
  array_roundtrip _ _ PV_B1_CarrierWide.from_to xs

def toRow (r : Array (Array HQ 2#usize) 2#usize) :
    Array (Array PV_B1_258.aspis_core.field.QM31 2#usize) 2#usize :=
  arrayMap (arrayMap PV_B1_Carrier258.toQ) r
def fromRow (r : Array (Array PV_B1_258.aspis_core.field.QM31 2#usize) 2#usize) :
    Array (Array HQ 2#usize) 2#usize := arrayMap (arrayMap PV_B1_Carrier258.fromQ) r

theorem row_inverse (r : Array (Array HQ 2#usize) 2#usize) : fromRow (toRow r)=r := by
  apply array_roundtrip
  intro pair
  exact array_roundtrip _ _ PV_B1_Carrier258.from_to pair

theorem pole_input (xs : Slice (Array (Array HQ 2#usize) 2#usize)) :
    sliceMap fromRow (sliceMap toRow xs)=xs := slice_roundtrip _ _ row_inverse xs
#print axioms sum_input
#print axioms powers_output
#print axioms row_inverse
#print axioms pole_input
end PV_B1_CarrierContainers
