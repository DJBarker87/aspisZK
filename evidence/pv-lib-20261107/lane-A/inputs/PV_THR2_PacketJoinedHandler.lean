import PV_THR2_PacketBoxImageAway
import PV_THR2_IntrinsicSemantics_NonNullAsRef
set_option autoImplicit false
noncomputable section
namespace PV_THR2_PacketJoinedHandler
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
/-- One fixed native handler for all three Packet intervals. The two stores
are the explicit actual issued124 and reached126 stores; this definition does
not replace any source store or assert that original entry already uses it. -/
def handler (B : Carrier OWNER Data) (resources : Resources) (encode : Encode)
    (constructorStore derefStore : Store Data)
    (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data) :=
  PV_THR2_PacketPointerBoxReplies.handler resources encode constructorStore shape
    (PV_THR2_IntrinsicSemantics_NonNullAsRef.handler B derefStore H)
/-- Symbolic agreement outside the five named native semantics tokens. No
returned case, source read or endpoint hypothesis is introduced. -/
theorem away (B : Carrier OWNER Data) (resources : Resources) (encode : Encode)
    (constructorStore derefStore : Store Data)
    (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (fn input : Data) (a : Nat) (w : OWNER)
    (nBox : fn ≠ PV_THR2_Packet124BoxIssue17.fn)
    (n217 : fn ≠ PV_THR2_Packet124ReturnData.intoFn)
    (n312 : fn ≠ PV_THR2_Packet216Children.fn5)
    (n313 : fn ≠ PV_THR2_Packet216Children.fn15)
    (n320 : fn ≠ PV_THR2_PacketInner320.fn) :
    handler B resources encode constructorStore derefStore shape H (.child fn a [input]) w =
      H (.child fn a [input]) w := by
  unfold handler PV_THR2_PacketPointerBoxReplies.handler
  rw [PV_THR2_PacketBoxImageAway.child _ _ _ _ _ _ _ _ _ nBox]
  rw [PV_THR2_PacketPointerSemantics.away _ _ _ _ _ n217 n312 n313]
  exact PV_THR2_IntrinsicSemantics_NonNullAsRef.away _ _ _ _ _ _ _ n320
#print axioms handler
#print axioms away
end PV_THR2_PacketJoinedHandler
