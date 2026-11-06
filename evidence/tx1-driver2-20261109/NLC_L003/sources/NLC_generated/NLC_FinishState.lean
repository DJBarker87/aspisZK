import NKQ_FinishStages
import NHZ_NativeAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Q := aspis_core.field.QM31
abbrev Alpha := Array Q 10#usize
abbrev Claims := Array (Array Q 29#usize) 3#usize
abbrev Words := Array Q 29#usize
abbrev Low := Array Q 16#usize
abbrev High := Array Q 10#usize
abbrev Point := aspis_core.circle.SecureCirclePoint
abbrev Out (H : Type) := core.result.Result (r1_semantic.Verified H) r1_wire.Error
/-- Original inputs are retained through every state; no independent input is selected. -/
structure Input (H : Type) where
 reservation : NP6_StdModel.Reservation
 digest : aspis_core.Digest32 H
 publicValue : pool_v1.pair_forest_semantic_terminal.r0.Public
 prefix1 : r1_wire.Prefix
 transcript : r1_wire.SemanticTranscript H
 challenges : r1_wire.Challenges
/-- Owned local slots. An uninitialized slot is never silently defaulted. -/
structure Locals (H : Type) where
 running : Option Q := none
 alpha : Option Alpha := none
 transcript : Option (r1_wire.SemanticTranscript H) := none
 claims : Option Claims := none
 terminal : Option Q := none
 low : Option Low := none
 high : Option High := none
 blind : Option Q := none
 mask : Option Q := none
 extra : Option Words := none
 product : Option Q := none
 partialValue : Option Q := none
 masked : Option Q := none
 stateBefore : Option (Array U8 32#usize) := none
 z0 : Option Point := none
 beforeZ1 : Option Words := none
 z1 : Option Point := none
 root : Option (Array U8 32#usize) := none
/-- Separate repeated source occurrences; arguments are read from the SAME state. -/
inductive Event where
 | rounds | mark2 | claims | original | terminal | mapPublic | mark3
 | lowArray | lowIndex | highArray | highIndex | blind | alpha | mask
 | record25a | decode25 | multiply | addMask | extra28 | addExtra | terminalGuard
 | mark4 | stateBefore | record25b | circle0 | record26a | decode26
 | record26b | circle1 | mark5 | circleGuard | payload2 | rootCopy | verified
 deriving DecidableEq, Repr
/-- One parent state, rather than unrelated successful local executions. The
native association of these slots is OPEN until the cut transcriptions are installed. -/
structure State (H : Type) where
 input : Input H
 locals : Locals H
 next : Event
abbrev Post (H : Type) := Sum (Out H) (State H)

def setNext {H : Type} (s : State H) (e : Event) : State H := {s with next := e}
def put {H : Type} (s : State H) (e : Event) (l : Locals H) : State H := {s with locals := l, next := e}
/-- Full immutable input frame, including original transcript/hash carrier. -/
def InputFrame {H : Type} (before after : State H) : Prop := after.input = before.input

theorem setNext_frame {H : Type} (s : State H) (e : Event) : InputFrame s (setNext s e) := rfl
theorem put_frame {H : Type} (s : State H) (e : Event) (l : Locals H) : InputFrame s (put s e l) := rfl
#print axioms setNext_frame
#print axioms put_frame
end AspisR1.NLC_Finish
end
