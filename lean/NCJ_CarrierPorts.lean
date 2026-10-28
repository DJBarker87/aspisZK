import FIo_FieldBridge
set_option autoImplicit false
namespace NCJ_CarrierPorts
open Aeneas Aeneas.Std Result AspisR1
abbrev E := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
abbrev NE := FIo_Install.NE

theorem to_from (x : NE) : FIo_Install.toE (FIo_Install.fromE x)=x := rfl

theorem from_to (x : E) : FIo_Install.fromE (FIo_Install.toE x)=x := rfl

theorem injective_from (x y : NE) (h : FIo_Install.fromE x=FIo_Install.fromE y) : x=y := by
  have same:=congrArg FIo_Install.toE h
  simpa only [to_from] using same

theorem exact_wide (x : E) : FIo_FieldBridge.wide (FIo_Install.toE x)=SAQ_WideABI.toW x := rfl

/-- The coordinate-only result projection is injective; equal mathematical
outputs alone are never used as an unproved raw carrier identity. -/
theorem exact_return (native : NE) (model : E) :
    FIo_Install.fromE native=model ↔ native=FIo_Install.toE model := by
  constructor
  · intro h
    have same:=congrArg FIo_Install.toE h
    simpa only [to_from] using same
  · intro h
    simpa only [h,from_to]

#print axioms to_from
#print axioms from_to
#print axioms injective_from
#print axioms exact_wide
#print axioms exact_return
end NCJ_CarrierPorts
