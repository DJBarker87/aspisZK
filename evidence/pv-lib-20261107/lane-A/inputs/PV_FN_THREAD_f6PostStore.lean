import PV_THR2_InlineChildReturn
import PV_FN_THREAD_f6LoopReplies
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6PostStore
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- A BODY reply is delivered on its explicit Post store. This definition
selects no reply branch and asserts no body execution or store equality. -/
def deliver {W E : Type} (B : Carrier W Data) (c : Config)
    (wait : PV_STX2_Native.Waiting Data) (post : Store Data) (r : Reply W E Data) :=
  PV_THR2_ChildBoundary.delivered B {c with store := post} wait r

/-- Return administration writes only the actual child return slot and caller
return destination, over the callee's Post store. Never substitute the issuance
store or construct a BODY store using StaticReply.returnedStore. -/
theorem returned {W E : Type} (B : Carrier W Data) (c : Config)
    (wait : PV_STX2_Native.Waiting Data) (post : Store Data) (child dest : Nat)
    (v : Data) (w : W) (es : List E)
    (action : wait.action = .child child (.local dest)) :
    deliver B c wait post ⟨.returned (.ok v),w,es⟩ =
      ⟨.running ⟨{c.frame with waiting := none},c.callers,
        write (write post ⟨child,0,[]⟩ (some v))
          ⟨c.frame.activation,dest,[]⟩ (some v)⟩,w,es⟩ := by
  exact PV_THR2_InlineChildReturn.delivered_success B {c with store := post}
    wait child dest v w es action

/-- The incoming frame is a callee Post projection. Only the two actual return
slots are excluded in addition; there is no inferred global world frame. -/
theorem frame (before post : Store Data) (child a dest : Nat) (v : Data)
    (q : Address) (callee_frame : post.cells q = before.cells q)
    (child_slot : q ≠ (⟨child,0,[]⟩ : Address))
    (caller_slot : q ≠ (⟨a,dest,[]⟩ : Address)) :
    (write (write post ⟨child,0,[]⟩ (some v)) ⟨a,dest,[]⟩ (some v)).cells q =
      before.cells q := by
  simp only [write,child_slot,caller_slot,ite_false]
  exact callee_frame

/-- The destination-cell fact required by f6's next own segment is derived
from return administration, rather than introduced as a caller Pre clause. -/
theorem destination (post : Store Data) (child a dest : Nat) (v : Data) :
    (write (write post ⟨child,0,[]⟩ (some v)) ⟨a,dest,[]⟩ (some v)).cells
      ⟨a,dest,[]⟩ = some v := by simp [write]

#print axioms returned
#print axioms frame
#print axioms destination
end PV_FN_THREAD_f6PostStore
