import PV_B1_Carrier254
set_option autoImplicit false
namespace PV_B1_CarrierWide
abbrev HW := PV_B1_Host.aspis_core.field.wide_exact.WideExact
abbrev W := PV_B1_254.aspis_core.field.wide_exact.WideExact

def toW (x : HW) : W := { c0 := PV_B1_Carrier254.toQ x.c0, c1 := PV_B1_Carrier254.toQ x.c1 }
def fromW (x : W) : HW := { c0 := PV_B1_Carrier254.fromQ x.c0, c1 := PV_B1_Carrier254.fromQ x.c1 }

theorem from_to (x : HW) : fromW (toW x)=x := by
  cases x
  simp only [fromW,toW,PV_B1_Carrier254.from_to]

theorem to_from (x : W) : toW (fromW x)=x := by
  cases x
  simp only [fromW,toW,PV_B1_Carrier254.to_from]

theorem injective (a b : HW) : toW a=toW b ↔ a=b := by
  constructor
  · intro h
    have hr := congrArg fromW h
    simpa only [from_to] using hr
  · intro h; cases h; rfl
#print axioms from_to
#print axioms to_from
#print axioms injective
end PV_B1_CarrierWide
