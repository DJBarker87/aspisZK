import PV_LIB_A_SequenceFrame14
import PV_THR2_IntrinsicFrameFull
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_NativeCellFrame14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_LIB_A_SourceCellFrame14

theorem issued (limit : Nat) (s : Store Data) (vs : List Data)
    (fresh : limit ≤ s.nextActivation) : Below limit s (PV_THR2_StaticCall.issued s vs) := by
  intro p hp
  exact PV_LIB_A_CallFrame13.issued_frame s vs p (by omega)

theorem returned_store (limit : Nat) (s : Store Data) (a dest : Nat) (vs : List Data) (v : Data)
    (caller : limit ≤ a) (fresh : limit ≤ s.nextActivation) :
    Below limit s (PV_THR2_StaticReply.returnedStore s a vs dest v) := by
  exact trans limit s (PV_THR2_StaticCall.issued s vs) _ (issued limit s vs fresh)
    (trans limit _ _ _ (write_frame limit _ ⟨s.nextActivation,0,[]⟩ (some v) fresh)
      (write_frame limit _ ⟨a,dest,[]⟩ (some v) caller))

/-- ALL native-reply arms frame older SOURCE cells on an ordinary local child
boundary. This makes no claim that an arbitrary native handler frames OWNER
memory, or that a missing source writer has adequate native semantics. -/
theorem full_reply (C : Carrier OWNER Data) (limit : Nat) (s : Store Data) (a dest : Nat)
    (parents : List Frame) (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (fn : Data) (vs : List Data) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (caller : limit ≤ a) (fresh : limit ≤ s.nextActivation) :
    Below limit s (PV_LIB_A_SequenceFrame14.storeOf
      (PV_THR2_IntrinsicFrameFull.received C s a parents loops rest fn vs dest r es stack).current.status) := by
  rcases r with ⟨answer,post,events⟩
  cases answer with
  | pending => exact issued limit s vs fresh
  | returned result =>
    cases result with
    | ok v => exact returned_store limit s a dest vs v caller fresh
    | fail e => cases parents <;> exact issued limit s vs fresh
    | div => cases parents <;> exact issued limit s vs fresh
  | fault f => cases f <;> exact issued limit s vs fresh

#print axioms issued
#print axioms returned_store
#print axioms full_reply
end PV_LIB_A_NativeCellFrame14
