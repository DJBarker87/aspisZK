import PV_THR2_PacketPointerBoxReplies
set_option autoImplicit false
noncomputable section
namespace PV_THR2_PacketBoxImageAway
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
/-- Symbolic handler agreement outside the exact BoxNew token, for arbitrary
argument shapes. No source-store reduction, return case or endpoint premise. -/
theorem child (resources : Resources) (encode : Encode) (s : Store Data)
    (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (fn : Data) (a : Nat) (args : List Data) (w : OWNER)
    (other : fn ≠ PV_THR2_Packet124BoxIssue17.fn) :
    PV_THR2_PacketBoxImageHandler.handler resources encode s shape H (.child fn a args) w =
      H (.child fn a args) w := by
  unfold PV_THR2_PacketBoxImageHandler.handler
  split <;> simp_all only [PV_STX2_Native.Request.child.injEq,not_false_eq_true, false_and,if_false]
#print axioms child
end PV_THR2_PacketBoxImageAway
