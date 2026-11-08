import PV_STX2_ToVecCallAtChild
import PV_STX2_Source7LayoutGlobals
set_option autoImplicit false
noncomputable section
namespace PV_STX2_ToVecCallSummaryStart
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER
/-- Conditional on owner acceptance of the translator patch. The call-entry
summary's completed initial segment: actual f13-created f21 captures, nineteen
installed source transitions, derived LOCAL8 registration and f35 entry. The
Layout operand is DISCHARGED by the existing static initializer fact; there is
no global/receiver/choice-equality premise. This is not the full to_vec return. -/
theorem source19 (resources : Resources) (encode : Encode)
    (base : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (store : Store Data) (parents : List Frame) (w : OWNER) (a : Nat)
    (p : Address) (length alloc : Data) (prior : List PV_RJ4IDB.NativeEvent) :
    let base' := PV_STX2_Source7LayoutGlobals.carrier base K H
    let layout := PV_STX2_Source7LayoutConstructor.value
    let start := PV_STX2_SliceCloneBorrow.childConfig store parents a (PV_STX2_TypedReferences.reference p length) alloc
    let c := PV_STX2_ToVecCallDispatch.entered (PV_STX2_SliceToVecEntry.prepared start.store start.frame.activation length)
      start.callers start.frame.activation length alloc layout
    PV_STX2_Source7IterationBindings.advance resources encode
      (PV_STX2_Source7ConstructorEntry.carrier (PV_STX2_SliceClonePointers.carrier base'))
      K (PV_STX2_Source7QAllocationDispatch.dispatch P) H 19 ⟨.running start,w,prior⟩ =
      ⟨.running (PV_STX2_ToVecConstructorDispatch.entered c.store c.callers c.frame.activation
        length alloc layout),PV_STX2_ToVecCallRegister.registered w start.frame.activation,prior⟩ := by
  dsimp only
  apply PV_STX2_ToVecCallAtChild.source19
  exact PV_STX2_Source7LayoutGlobals.actual_global base K H w
#print axioms source19
end PV_STX2_ToVecCallSummaryStart
