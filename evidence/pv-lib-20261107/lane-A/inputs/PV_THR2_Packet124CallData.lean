import PV_THR2_PacketEnter124
set_option autoImplicit false
namespace PV_THR2_Packet124CallData
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Actual12801 operand move and structured124 entry, with full saved caller. -/
def moved (s : Store Data) (a : Nat) := write s ⟨a,18,[]⟩ none
def entered (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame) (packet : Data) :=
  PV_THR2_IntrinsicFrameEnter.entered (moved s a) a parents loops
    (PV_THR2_F361.live.body.drop 59) PV_THR2_Source361PacketChildren.fn58 [packet] 17 PV_THR2_F124.live
/-- Child124 argument derives from actual source call issuance. -/
theorem argument (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame) (packet : Data) :
    (entered s a parents loops packet).store.cells
      ⟨(entered s a parents loops packet).frame.activation,1,[]⟩ = some packet := by
  simp [entered,moved,PV_THR2_IntrinsicFrameEnter.entered,PV_THR2_IntrinsicFrameEnter.pending,
    PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write]
/-- The actual fresh124 activation is below the issued nextActivation. -/
theorem fresh (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame) (packet : Data) :
    (entered s a parents loops packet).frame.activation < (entered s a parents loops packet).store.nextActivation :=
  Nat.lt_succ_self _
/-- Exact12801 saved caller child action, never a selected destination premise. -/
theorem action (s : Store Data) (a : Nat) (packet : Data) :
    (PV_THR2_StaticReply.wait (moved s a) PV_THR2_Source361PacketChildren.fn58 [packet] 17).action =
      .child (moved s a).nextActivation (.local 17) := rfl
#print axioms argument
#print axioms fresh
#print axioms action
end PV_THR2_Packet124CallData
