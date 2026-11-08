import PV_LIB_Graph
import PV_W1_OwnerNativeFrame
set_option autoImplicit false
namespace PV_LIB_Registry
open PV_STX_Machine PV_STX2_Syntax PV_EVHB_OwnerMachine
open PV_W1_OwnerNativeFrame

def observeReply {E : Type} (r : Reply OWNER E Data) : PV_LIB.Observation (Answer Data) OWNER E :=
  match r.answer with
  | .fault .abort => .abort r.events
  | _ => .returned r.answer r.world r.events

def model {E : Type} (H : Backend E) (request : PV_STX2_Native.Request Data) (w : OWNER) :=
  observeReply (PV_THR2_OwnUniformResourceHandler.lift H request w)
def law {E : Type} (H : Backend E) (request : PV_STX2_Native.Request Data) (w : OWNER)
    (out : PV_LIB.Observation (Answer Data) OWNER E) : Prop := out = model H request w

def Frame {E : Type} (w : OWNER) : PV_LIB.Observation (Answer Data) OWNER E → Prop
  | .abort _ => True
  | .returned _ post _ => post.places = w.places ∧ post.next = w.next

/-- Native environments have no channel into ghost places/next. This graph
retains every full answer and exposes only events at process abort. Allocation
and other explicit OWNER actions are separate model functions. -/
theorem certified {E : Type} (H : Backend E) (request : PV_STX2_Native.Request Data) (w : OWNER) :
    law H request w (observeReply (PV_THR2_OwnUniformResourceHandler.lift H request w)) ∧
    ∀ out, law H request w out → Frame w out := by
  refine ⟨rfl,?_⟩
  intro out h
  change out = model H request w at h
  rw [h]
  unfold model observeReply
  split
  · trivial
  · exact ⟨rfl,rfl⟩
#print axioms certified
end PV_LIB_Registry
