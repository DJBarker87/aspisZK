import PV_STX2_LiveNumbering
import PV_THR2_F0
set_option autoImplicit false
namespace PV_LIB_A_Numbering
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_STX2_LiveNumbering
/-- The actual outer thread program entry has no additional numbering premise. -/
theorem original_entry (captures : List Data) (s : Store Data) :
    Numbered (enter PV_THR2_F0.live captures s) := initial _ _ _
/-- Caller discharge uses the provider's generic push theorem literally. -/
theorem child_entry (c : Config) (program : PV_STX2_SliceSyntax.Program)
    (callee : Data) (b : Nat) (vs : List Data) (q : PV_STX2_Native.Waiting Data)
    (numbered : Numbered c) (waiting : c.frame.waiting = some q)
    (request : q.request = .child callee b vs) :
    Numbered {c with frame := {activation := b,remaining := program.body},callers := c.frame :: c.callers} :=
  push c program callee b vs q numbered waiting request
/-- Convert the generic decreasing-chain clause into the literal lower-frame
bounds required by older CLOSED Arc providers. No counter equality. -/
theorem lower_bound (c : Config) (numbered : Numbered c) (f : Frame)
    (member : f ∈ c.callers) : f.activation < c.store.nextActivation :=
  Nat.lt_trans (caller_older numbered.2.2 f member) numbered.1
#print axioms original_entry
#print axioms child_entry
#print axioms lower_bound
end PV_LIB_A_Numbering
