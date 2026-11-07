import NMS_RowSpec233
import NLM_Validate242
set_option autoImplicit false
noncomputable section
namespace NMS_RowSpec242
open Aeneas Aeneas.Std AdapterRw NMS_OwnedPackets
abbrev World := NLM_PacketTypes.World
abbrev Request := NLM_Validate242.Request
abbrev Args := NMN_242Interface.Args
abbrev RawEvent := NLM_Validate242.Event
/-- Box-bearing occurrences cannot be hidden in a value-only plain event. -/
def Plain : RawEvent → Prop
 | .authenticate .. => False
 | .scan .. => False
 | .reconstruct .. => False
 | _ => True

def mapReply {A B : Type} (f : A → B) :
 Result (core.result.Result A PE) → Result (core.result.Result B PE)
 | .ok (.Ok a) => .ok (.Ok (f a))
 | .ok (.Err e) => .ok (.Err e)
 | .fail e => .fail e
 | .div => .div

inductive Event (Ambient : Type) where
 | plain (event : RawEvent) (ordinary : Plain event)
 | authenticate (args : NMS_RowSpec233.Args) (before : World Ambient)
   (endState : NMS_RowSpec233.Outcome (World Ambient))
 | scan (bytes : Slice U8) (reply : Result (core.result.Result Scanned PE))
 | reconstruct (request : Request) (auth : Auth) (candidate : Box Candidate)
   (reply : Result (core.result.Result (Box Statement) PE))

def Event.erase {Ambient : Type} : Event Ambient → RawEvent
 | .plain e _ => e
 | .authenticate a _ e => .authenticate a.program a.accounts a.pool a.lane a.slot
   ⟨mapReply Auth.erase e.value,e.events⟩
 | .scan bytes reply => .scan bytes (mapReply Scanned.erase reply)
 | .reconstruct request auth candidate reply =>
   .reconstruct request auth.erase candidate.payload (mapReply Box.payload reply)

/-- Returning owners remain fresh and the full external frame is preserved.
The stopped case has no post-world condition, because it has no post-world. -/
def Event.Owners {Ambient : Type} (inputs : List Nat) : Event Ambient → Prop
 | .plain _ _ => True
 | .authenticate _ before (.returned (.Ok auth) post _) =>
   auth.Fresh inputs ∧ post = before
 | .authenticate _ before (.returned (.Err _) post _) => post = before
 | .authenticate _ _ (.stopped _ _) => True
 | .scan _ (.ok (.Ok s)) => s.candidate.owner ∉ inputs
 | .scan _ _ => True
 | .reconstruct _ auth candidate (.ok (.Ok box)) =>
   box.owner ∉ inputs ∧ box.owner ∉ auth.owners ∧ box.owner ≠ candidate.owner
 | .reconstruct _ _ _ _ => True

/-- Full owner argument association at reconstruction, at its SAME call.
The erased source trace additionally fixes the unique occurrence and order. -/
def Linked {Ambient : Type} (events : List (Event Ambient)) : Prop :=
 ∀ request auth candidate reply,
  Event.reconstruct request auth candidate reply ∈ events →
  (∃ a before childEvents,
   Event.authenticate a before (.returned (.Ok auth) before childEvents) ∈ events) ∧
  (∃ bytes length,
   Event.scan bytes (.ok (.Ok ⟨candidate,length⟩)) ∈ events)

abbrev Outcome (Ambient : Type) := End (World Ambient) (Event Ambient) Validated
abbrev Native (Ambient : Type) := Args → World Ambient → Outcome Ambient

def Law {Ambient : Type} (inputs : List Nat) (before : World Ambient)
 (source : NJU_Log.Run RawEvent (core.result.Result r1_pool_adapter.ValidatedAsqa PE))
 (outcome : Outcome Ambient) : Prop :=
 outcome.events.map Event.erase = source.events ∧
 (∀ event ∈ outcome.events, event.Owners inputs) ∧ Linked outcome.events ∧
 match outcome with
 | .returned (.Ok validated) post events =>
   source.result = .ok (.Ok validated.erase) ∧ post = before ∧
   validated.statement.owner ∉ inputs ∧
   ∃ request auth candidate,
    Event.reconstruct request auth candidate (.ok (.Ok validated.statement)) ∈ events
 | .returned (.Err error) post _ =>
   source.result = .ok (.Err error) ∧ post = before
 | .stopped _ (.failed error) => source.result = .fail error
 | .stopped _ .diverged => source.result = .div

/-- Complete OPEN242 packet. The returned statement Box is the reconstruction
reply itself, not an independently chosen equal payload. All returned errors,
external frames, ordered prefixes and intermediate boxed arguments survive. -/
def RowSpec_242 {Ambient CoreError : Type}
 (missing : AspisR1.IDa_Deployed.Uninstalled CoreError) (indexError : CoreError)
 (reservation : AspisR1.NP6_StdModel.Reservation)
 (inputOwners : Args → List Nat) (native : Native Ambient) : Prop :=
 ∀ a before, Law (inputOwners a) before
  (NLM_Validate242.G (NLM_DeployedOps.ops missing indexError reservation)
   a.program a.accounts a.data a.slot) (native a before) ∧
 mapReply Validated.erase (native a before).value =
  r1_pool_adapter.owned.validate_asq8
   (NLM_DeployedOps.ops missing indexError reservation)
   a.program a.accounts a.data a.slot

/-- Unlike the earlier draft, a stopped arm exposes only the prefix. -/
theorem stopped_prefix {Ambient : Type} (inputs : List Nat) (before : World Ambient)
 (source : NJU_Log.Run RawEvent (core.result.Result r1_pool_adapter.ValidatedAsqa PE))
 (events : List (Event Ambient)) (cause : Stop)
 (law : Law inputs before source (.stopped events cause)) :
 events.map Event.erase = source.events := law.1
#print RowSpec_242
#print axioms stopped_prefix
end NMS_RowSpec242
