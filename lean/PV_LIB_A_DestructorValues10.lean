import PV_LIB_A_WeakGuardCaller9
import PV_LIB_A_TypedBody661
set_option autoImplicit false
namespace PV_LIB_A_DestructorValues10
open PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine

/-- Source unit is an empty value, never a physical allocation byte image. -/
def unitValue : Data := PV_THR2_KeyValues.pack PV_LIB_A_GenericDropMachine.unitTag []

/-- The original interpreter already uses this named aggregate completion on
undefined aggregate instructions. Make the SAME value interpretation available
at destructor dispatch and free polling, which bypass that fallback. -/
def carrier (C : Carrier OWNER Data) (b : Bool) : Carrier OWNER Data :=
  PV_THR2_AggregateCompletion.carrier (PV_THR2_OwnInitExactReturnedCases.carrier C b)

def metadata : Data :=
  match PV_LIB_A_TypedBody661.node4 [] with
  | .leaf (.bind _ _ (.reference _ (.constant m))) => m
  | _ => .null

theorem literal (C : Carrier OWNER Data) (b : Bool) :
    (carrier C b).constant metadata = some .null := rfl

theorem reference (C : Carrier OWNER Data) (b : Bool) (p : Address) (m : Data) (w : OWNER) :
    (carrier C b).dereference w ((carrier C b).reference p m) = some p := by
  change (PV_STX2_TypedReferences.carrier _).dereference w
    (PV_STX2_TypedReferences.reference p m) = some p
  exact PV_STX2_TypedReferences.dereference _ w p m

theorem aggregate (C : Carrier OWNER Data) (b : Bool) :
    (carrier C b).aggregate PV_LIB_A_GenericDropMachine.unitTag [] = some unitValue := rfl

/-- Checked obstruction to using the previous free layer with the original
carrier directly: the original aggregate operation has NO unit constructor. -/
theorem original_unit_missing (C : Carrier OWNER Data) (b : Bool) :
    (PV_THR2_OwnInitExactReturnedCases.carrier C b).aggregate
      PV_LIB_A_GenericDropMachine.unitTag [] = none := rfl

#print axioms unitValue
#print axioms carrier
#print axioms metadata
#print axioms literal
#print axioms reference
#print axioms aggregate
#print axioms original_unit_missing
end PV_LIB_A_DestructorValues10
