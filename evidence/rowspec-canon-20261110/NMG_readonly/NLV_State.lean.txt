import NLJ_RowSpec094
import NLJ_Tx1State
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Physical ownership bookkeeping; the source value alone never establishes
that a pointer is live, an allocation is initialized, or cleanup has run. -/
inductive OwnedKind where
 | scratch | prepared | accumulator | weights | geometry | inverses | lineZ
 | pending | raw | checkpoint
 deriving DecidableEq, Repr
structure Allocation where
 address : Nat
 bytes : List U8
 capacity : Nat
 alignment : Nat
 initialized : Nat
 live : Bool
structure Ownership where
 allocations : OwnedKind → Option Allocation
 shared : OwnedKind → Nat
 exclusive : OwnedKind → Bool
/-- ONE TX1 parent state, containing the owned value carriers in Local and
physical allocations, original external bytes/metadata/authorities and the
chronological attempted digest prefix. Physical interpretation is OPEN. -/
structure State where
 core : NLJ_Tx1.State
 external : NLJ_Packets.Frame094
 ownership : Ownership
 attempted : SdkC_Source.Log
/-- One event type, recording the entire SAME pre-state as well as its source
occurrence. Invocation constructs this from its own pre-state, never a free ID. -/
structure Event where
 pre : State
 kind : NLJ_Tx1.Event
def event (s : State) : Event := ⟨s,NLJ_Tx1.event s.core⟩
/-- No late read of proof/public replaces the original snapshots. -/
def InputAdmission (s : State) : Prop :=
 s.external.proof=s.core.input.proof ∧
 s.external.publicBytes=s.core.input.publicBytes
/-- Source-only projection, not a claim that Rust preserves every field. -/
def valueAdvance (s : State) (nextLocal : NLJ_Tx1.Local) : State :=
 {s with core:=NLJ_Tx1.advance s.core nextLocal}
theorem input_frame (s : State) (nextLocal : NLJ_Tx1.Local) :
 (valueAdvance s nextLocal).core.input=s.core.input := rfl
theorem external_frame (s : State) (nextLocal : NLJ_Tx1.Local) :
 (valueAdvance s nextLocal).external=s.external := rfl
theorem admission (s : State) (nextLocal : NLJ_Tx1.Local) (h : InputAdmission s) :
 InputAdmission (valueAdvance s nextLocal) := h
#print axioms input_frame
#print axioms external_frame
#print axioms admission
end AspisR1.NLV
end
