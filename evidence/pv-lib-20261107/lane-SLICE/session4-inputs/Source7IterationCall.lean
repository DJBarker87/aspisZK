import PV_STX2_Source7IterationBindings
import PV_STX2_Source7QUniformAgreement2
import PV_STX2_Source7QUniformCall
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7IterationCall
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER
/-- Conditional on owner acceptance of the translator patch. The new installed
interpreter consumes the existing generic registering call BY NAME, with the
actual iteration's store, parents, activation and OWNER pre-state. The local
operand facts are internal cuts; this is not a completed iteration theorem. -/
theorem source1 (resources : Resources) (encode : Encode)
    (base : Carrier OWNER Data) (ctrl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (store : Store Data) (parents : List Frame) (w : OWNER) (a : Nat)
    (length alloc layout : Data)
    (lengthOperand : store.cells ⟨a,3,[]⟩ = some length)
    (allocOperand : store.cells ⟨a,2,[]⟩ = some alloc)
    (layoutOperand : (PV_STX2_SliceClonePointers.carrier base).global w 3 = some layout) :
    PV_STX2_Source7IterationBindings.step resources encode
      (PV_STX2_SliceClonePointers.carrier base) ctrl programs handler
      ⟨{activation := a,remaining := PV_STX2_SliceF21.program.body.drop 9},parents,store⟩ w =
      ⟨.running (PV_STX2_SliceToVecEntry.called store parents a length alloc layout),
        PV_EVHB_SourceLifetimes.newAt w
          (PV_STX2_Source7QBinding.ownerPlace ⟨a,8,[]⟩)
          PV_STX2_Source7QResultLocal.shape
          (PV_EVHB_OwnerReserve.alignment PV_STX2_Source7QResultLocal.shape.align),[]⟩ := by
  unfold PV_STX2_Source7IterationBindings.step
  rw [PV_STX2_Source7QUniformAgreement2.step _ _ _ _ _ _ (by rfl)]
  exact PV_STX2_Source7QUniformCall.source1 base ctrl programs _ store parents w a
    length alloc layout lengthOperand allocOperand layoutOperand
#print axioms source1
end PV_STX2_Source7IterationCall
