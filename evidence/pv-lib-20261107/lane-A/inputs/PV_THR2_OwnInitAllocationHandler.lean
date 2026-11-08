import PV_THR2_OwnInitSourceCodec
import PV_THR2_OwnInitAllocationSelection
import PV_THR2_OwnInitAllocationReply
import PV_THR2_Source361InitChildren
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitAllocationHandler
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax
open PV_EVHB_OwnerMachine PV_EVHB_RawVecOwner PV_EVHB_OwnerHeap PV_OWN2_Codec
open scoped Classical
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Interpret ONLY the named14756 allocation child with a decoded ThreadInit
operand and the actual source-minted descriptor. Every other full reply stays
the native fallback's. Installation into the original-entry run remains open. -/
def handler (resources : Resources) (encode : Encode)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (request : PV_STX2_Native.Request Data) (s : OWNER) : Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  match request with
  | .child fn _ [payload] =>
    if fn=PV_THR2_Source361InitChildren.fnAllocationFull then
      match PV_THR2_OwnInitSourceCodec.decode payload,
          lookup s.world (PV_THR2_OwnInitAllocationSelection.id s) with
      | some words,some h => PV_THR2_OwnInitAllocationReply.reply resources encode s
          (PV_THR2_OwnInitAllocationSelection.id s) h words
      | _,_ => fallback request s
    else fallback request s
  | _ => fallback request s
/-- Conditional on owner acceptance of amended translator. Hypothesis: only
the source-derived frame. Allocation id/header and all three decoded operand
words are derived; no receiver or successful native reply is supplied. -/
theorem at_site (resources : Resources) (encode : Encode)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (activation : Nat) (handle callback vtable : Pointer)
    {s : OWNER} {a id : Nat} {h : Header}
    (frame : PV_THR2_OwnUniformReceiverFrame.Frame a id h s) :
    handler resources encode fallback
      (.child PV_THR2_Source361InitChildren.fnAllocationFull activation
        [PV_THR2_OwnInitFieldCodec.init handle callback vtable]) s =
      PV_THR2_OwnInitAllocationReply.reply resources encode s id h ⟨handle,callback,vtable⟩ := by
  have selected := PV_THR2_OwnInitAllocationSelection.selected frame
  simp only [handler,ite_true,PV_THR2_OwnInitSourceCodec.roundtrip,selected.1,frame.header]
/-- Conditional on owner acceptance of amended translator. Hypothesis: the
request is another child's actual function token. Full fallback worlds/events
and every failure are retained without any reply identity assumption. -/
theorem away (resources : Resources) (encode : Encode)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (fn payload : Data) (activation : Nat) (s : OWNER)
    (different : fn ≠ PV_THR2_Source361InitChildren.fnAllocationFull) :
    handler resources encode fallback (.child fn activation [payload]) s =
      fallback (.child fn activation [payload]) s := by
  simp only [handler,if_neg different]
#print axioms at_site
#print axioms away
end PV_THR2_OwnInitAllocationHandler
