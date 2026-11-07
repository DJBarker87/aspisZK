import NLI_SourceEquality
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Input := NLC_Finish.Input
abbrev Machine := NLC_Finish.State
abbrev Out := NLC_Finish.Out
/-- Linear ownership state of the single Claims allocation. Stack arrays and
borrowed public/prefix are values of the SAME machine, never extra heaps.
This is a proposed parent carrier until native cut transcriptions are installed. -/
inductive Owner where
 | absent | live | transferred | dropped
 deriving DecidableEq, Repr
/-- Reservation is carried in machine.input, exactly as NKU.Frame; there is
no second allocator outcome, free operation dictionary or selected reply. -/
structure State (H : Type) where
 machine : Machine H
 owner : Owner
/-- Heap actions refer to this invocation's SAME reservation. Child-internal
allocation/error cleanup is retained as one child action; parent releases only
an already live returned owner. Abort is a prefix, never an invented Drop. -/
inductive Event where
 | occurrence (site : NLC_Finish.Event)
 | digest (event : PreparedHashCode.Event)
 | claims (reservation : NP6_StdModel.Reservation)
 | acquire | borrow | release | transfer
abbrev Returned (H : Type) := Out H × Owner
abbrev Post (H : Type) := Sum (Returned H) (State H)
structure Observation (H : Type) where
 input : Input H
 events : List Event
 reply : Result (Returned H)
structure StepObservation (H : Type) where
 input : Input H
 events : List Event
 reply : Result (Post H)
def initial {H : Type} (input : Input H) : State H := ⟨NLC_Finish.initial input,.absent⟩
def erasePost {H : Type} : Post H → NLC_Finish.Post H
 | .inl out => .inl out.1
 | .inr s => .inr s.machine
def eraseReply {H : Type} (r : Result (Returned H)) : Result (Out H) := do
 let out ← r
 ok out.1
end AspisR1.NLU
end
