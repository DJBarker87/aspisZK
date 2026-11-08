import PV_LIB_Observation
import PV_FN_SLICE_f7_DestructorBinding
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SLICE_TypedDrop
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine

/-- The exact typed f22 body at its own completion, before return administration.
This is support for source178, not the full f7 runtime-Drop suffix. -/
def model (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB.observe (PV_FN_SLICE_f22_TypedDestructor.state
    (PV_FN_SLICE_f22_TypedDestructor.finalStore s a) a parents w es stack 3)

def law (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model s a parents w es stack

theorem certified (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    law s a parents w es stack (PV_LIB.observe
      (PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier C) K P H 3
        (PV_FN_SLICE_f22_TypedDestructor.state s a parents w es stack 0))) :=
  congrArg PV_LIB.observe (PV_FN_SLICE_f22_TypedDestructor.run C K P H s a parents w es stack)

theorem selected : PV_STX2_ChainCaptures.regular
    (.object [("Regular",PV_FN_SLICE_f7_Drop.source)]) = some 22 :=
  PV_FN_SLICE_f7_DestructorBinding.selected

#print axioms certified
#print axioms selected
end PV_LIB_SLICE_TypedDrop
