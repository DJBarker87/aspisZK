import PV_LIB_Observation
import PV_W5_NativeLeaves
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SliceNativeGraph
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER
open PV_W5_LeafBoundary
/-- Literal output function in the CLOSED slice leaf provider's Post. -/
def internalModel (C : Carrier OWNER Data) (e : Entry) (callee : Data)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) :=
  deliver C e callee (PV_STX2_Source7QUniformResourceHandler.lift H
    (.child callee e.store.nextActivation e.arguments) w) prior

def model (C : Carrier OWNER Data) (e : Entry) (callee : Data)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) :=
  PV_LIB.observe (⟨internalModel C e callee H w prior,stack⟩ :
    PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)
#print axioms internalModel
#print axioms model
end PV_LIB_SliceNativeGraph
