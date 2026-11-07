import PV_THR2_PacketJoinedHandler
set_option autoImplicit false
noncomputable section
namespace PV_THR2_PacketJoinedHandlerAway
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
/-- Internal descriptor exclusions on the retained prefix. All arguments and
complete native outcomes stay arbitrary. No endpoint or returned-case premise. -/
def Other (fn : Data) : Prop :=
  fn ≠ PV_THR2_Packet124BoxIssue17.fn ∧
  fn ≠ PV_THR2_Packet124ReturnData.intoFn ∧
  fn ≠ PV_THR2_Packet216Children.fn5 ∧
  fn ≠ PV_THR2_Packet216Children.fn15 ∧
  fn ≠ PV_THR2_PacketInner320.fn
/-- Extend the existing singleton agreement to every argument list. Non-unary
calls use fallback by definition; no source operand or store is evaluated. -/
theorem child (B : Carrier OWNER Data) (resources : Resources) (encode : Encode)
    (constructorStore derefStore : Store Data)
    (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (fn : Data) (a : Nat) (args : List Data) (w : OWNER) (other : Other fn) :
    PV_THR2_PacketJoinedHandler.handler B resources encode constructorStore derefStore shape H
      (.child fn a args) w = H (.child fn a args) w := by
  rcases other with ⟨box,nn,raw,forget,asref⟩
  unfold PV_THR2_PacketJoinedHandler.handler PV_THR2_PacketPointerBoxReplies.handler
  rw [PV_THR2_PacketBoxImageAway.child _ _ _ _ _ _ _ _ _ box]
  cases args with
  | nil => rfl
  | cons input rest =>
    cases rest with
    | nil =>
      unfold PV_THR2_PacketPointerSemantics.handler
      rw [PV_THR2_IntrinsicSemantics_NonNullFrom217.away _ _ _ _ _ nn,
        PV_THR2_IntrinsicSemantics_BoxIntoRawWithAllocator312.away _ _ _ _ _ raw,
        PV_THR2_IntrinsicSemantics_MemForget313.away _ _ _ _ _ forget]
      exact PV_THR2_IntrinsicSemantics_NonNullAsRef.away _ _ _ _ _ _ _ asref
    | cons x xs => rfl
/-- Every non-child request is definitionally retained; child agreement uses
only the exact saved descriptor exclusions, for all argument shapes. -/
theorem request (B : Carrier OWNER Data) (resources : Resources) (encode : Encode)
    (constructorStore derefStore : Store Data)
    (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (r : PV_STX2_Native.Request Data) (w : OWNER)
    (other : ∀ fn a args, r = .child fn a args → Other fn) :
    PV_THR2_PacketJoinedHandler.handler B resources encode constructorStore derefStore shape H r w = H r w := by
  cases r with
  | child fn a args => exact child B resources encode constructorStore derefStore shape H fn a args w (other fn a args rfl)
  | copy source destination count => rfl
  | drop callee value => rfl
#print axioms request
#print axioms Other
#print axioms child
end PV_THR2_PacketJoinedHandlerAway
