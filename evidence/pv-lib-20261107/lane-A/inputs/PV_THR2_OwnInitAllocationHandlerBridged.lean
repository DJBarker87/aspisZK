import PV_THR2_OwnInitSourceCodecBridged
import PV_THR2_OwnInitAllocationHandler
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitAllocationHandlerBridged
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_STX_Machine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner
open scoped Classical
/-- New14756 interpretation only. The complete existing allocation reply is
reused, including null/abort, fault, failure, divergence, pending and all exact
world/event effects. This handler changes no source store. -/
def handler (resources : Resources) (encode : Encode)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (request : PV_STX2_Native.Request Data) (s : OWNER) : Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  match request with
  | .child fn _ [payload] =>
    if fn=PV_THR2_Source361InitChildren.fnAllocationFull then
      match PV_THR2_OwnInitSourceCodec.decodeBridged s payload,
          lookup s.world (PV_THR2_OwnInitAllocationSelection.id s) with
      | some words,some h => PV_THR2_OwnInitAllocationReply.reply resources encode s
          (PV_THR2_OwnInitAllocationSelection.id s) h words
      | _,_ => fallback request s
    else fallback request s
  | _ => fallback request s

theorem bare_agreement (resources : Resources) (encode : Encode)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s : OWNER) (a : Nat) (kind handle data vtable : Data) :
    handler resources encode fallback
      (.child PV_THR2_Source361InitChildren.fnAllocationFull a
        [PV_THR2_KeyValues.pack kind [handle,.array [data,vtable]]]) s =
    PV_THR2_OwnInitAllocationHandler.handler resources encode fallback
      (.child PV_THR2_Source361InitChildren.fnAllocationFull a
        [PV_THR2_KeyValues.pack kind [handle,.array [data,vtable]]]) s := by
  simp only [handler,PV_THR2_OwnInitAllocationHandler.handler,ite_true,
    PV_THR2_OwnInitSourceCodec.bare_agreement]
  rfl

theorem away (resources : Resources) (encode : Encode)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s : OWNER) (fn : Data) (a : Nat) (args : List Data)
    (different : fn ≠ PV_THR2_Source361InitChildren.fnAllocationFull) :
    handler resources encode fallback (.child fn a args) s = fallback (.child fn a args) s := by
  cases args with
  | nil => rfl
  | cons arg rest =>
    cases rest with
    | nil => simp only [handler,if_neg different]
    | cons arg2 rest => rfl

/-- Named, unproved interpretation adequacy obligation for Recount14.
source is the actual source/binary execution of14756 (including source cells),
interpretation is this handler followed by actual return administration on
that same store. Equality is of full reply AND full store, on every answer;
no decoder success or Shape premise narrows the obligation. Linkage of the
impl115 symbol is a separate binary-structural entry. No theorem below takes
this obligation as a hypothesis. -/
def InterpretationAdequacy14756
    (source interpretation : Config → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data × Store Data) : Prop :=
  ∀ c w, PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 129) c →
    source c w = interpretation c w
#print axioms bare_agreement
#print axioms away
end PV_THR2_OwnInitAllocationHandlerBridged
