import PV_LIB_A_Unique612
import PV_LIB_Registry
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_UniqueBinding
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
open PV_THR2_IntrinsicSemantics_UniqueNewUnchecked612
/-- Literal identity between the CLOSED root's emitted token and the
existing intrinsic semantics token; no erased generic descriptor lookup. -/
theorem callee (e : Entry) (raw : Data) :
    (PV_W1_NativeLeaves.entry612 e [raw]).callee = PV_THR2_BoxFromTable.fnUniqueFull := rfl

def model {E : Type} (H : Backend E) (e : Entry) (raw : Data) (w : OWNER) :=
  PV_LIB_Registry.observeReply (PV_THR2_OwnUniformResourceHandler.lift (handler H)
    (.child (PV_W1_NativeLeaves.entry612 e [raw]).callee e.store.nextActivation [raw]) w)
def law {E : Type} (H : Backend E) (e : Entry) (raw : Data) (w : OWNER)
    (out : PV_LIB.Observation (Answer Data) OWNER E) : Prop := out = model H e raw w
/-- Bind the actual612 request to the SAME provider handler and OWNER lift.
The ghost registry is framed by the existing lift, including stopped arms. -/
theorem installed {E : Type} (H : Backend E) (semantics : Fact H)
    (e : Entry) (raw : Data) (w : OWNER) :
    law H e raw w (PV_LIB_Registry.observeReply (PV_THR2_OwnUniformResourceHandler.lift H
      (.child (PV_W1_NativeLeaves.entry612 e [raw]).callee e.store.nextActivation [raw]) w)) := by
  have agree := PV_LIB_A_Unique612.installed H semantics (world w) e.store.nextActivation raw
  change H (.child PV_THR2_BoxFromTable.fnUniqueFull e.store.nextActivation [raw]) (world w) =
    handler H (.child PV_THR2_BoxFromTable.fnUniqueFull e.store.nextActivation [raw]) (world w) at agree
  unfold law model
  rw [callee]
  unfold PV_THR2_OwnUniformResourceHandler.lift
  rw [agree]
#print axioms callee
#print axioms installed
end PV_LIB_A_UniqueBinding
