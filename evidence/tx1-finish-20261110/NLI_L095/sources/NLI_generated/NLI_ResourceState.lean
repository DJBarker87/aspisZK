import NLI_SourceEquality
import NKA_ClaimsEffects
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Resource
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- Allocator/rest-heap interpretation plus the last allocation's owner.
The live Claims payload is separately represented by machine.locals.claims;
its unique owner is tracked below. This is a carrier target, not a proof of
its physical interpretation or of an enclosing native call. -/
abbrev Heap (A : Type) := A × Nat
structure State (A H : Type) where
 machine : NLC_Finish.State H
 heap : Heap A
 claimsOwner : Option Nat
abbrev Returned (A H : Type) := Out H × Heap A × Option Nat
abbrev Post (A H : Type) := Sum (Returned A H) (State A H)
/-- ONE event type for the extended parent. Digest attempts and failing
resource actions are kept in order, not only successful calls. -/
inductive Event (A : Type) : Type 1 where
 | occurrence : NLC_Finish.Event → Event A
 | digest : PreparedHashCode.Event → Event A
 | allocate : Heap A → Result (Heap A) → Event A
 | cleanup : Heap A → Result (Heap A) → Event A
structure Observation (A H : Type) : Type 1 where
 lastInput : Input H
 trace : List (Event A)
 reply : Result (Returned A H)
structure StepObservation (A H : Type) : Type 1 where
 lastInput : Input H
 trace : List (Event A)
 reply : Result (Post A H)
def initial {A H : Type} (heap : Heap A) (input : Input H) : State A H :=
 ⟨NLC_Finish.initial input,heap,none⟩
end AspisR1.NLI_Resource
end
