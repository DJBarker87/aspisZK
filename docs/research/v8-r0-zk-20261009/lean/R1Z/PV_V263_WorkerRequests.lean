import R1Z.PV_V263_World
/-! Typed, stateful worker OS answers. Callback values are never world answers.
The event codec is supplied explicitly: no claim that arbitrary encodings are
native observations. Allocator/std/TLS correspondence remains runtime adequacy.
This is a worker interpreter component, not the completed V263 installation. -/
set_option autoImplicit false
namespace R1Z.PV_V263_WorkerRequests
open Aeneas Aeneas.Std PV_V263_World
open PV_RJ4IDB (Bytes NativeEvent)

inductive SpawnAnswer where
  | granted (handle : Nat)
  | denied (code : Int)
 deriving DecidableEq

inductive Request : Type → Type where
  | tlsRead (thread : Nat) : Request Bool
  | tlsReplace (thread : Nat) (value : Bool) : Request Bool
  | tlsRestore (thread : Nat) (value : Bool) : Request Unit
  | allocate (site thread elements elementSize align : Nat) : Request Unit
  | release (site thread : Nat) : Request Unit
  | spawn (thread : Nat) : Request SpawnAnswer
  | join (thread handle : Nat) : Request (Option Bytes)
  | cleanup (thread : Nat) : Request Unit

structure Runtime (S : Type) where
  answer : {A : Type} → Request A → Q S A

/-- Explicit granting world for existential resource witnesses. This answers
primitive resource requests only; it does not supply successful callback values.
TLS and handles change state; all requests produce retained side events. -/
def grants {S : Type} (encode : {A : Type} → Request A → Bytes) : Runtime S where
  answer := fun {A} request w =>
    let events := [NativeEvent.side [118,50,54,51] (encode request)]
    match request with
    | .tlsRead t => ⟨.returned (.ok ((w.activeTLS.lookup t).getD false)),w,events⟩
    | .tlsReplace t b =>
      let old := (w.activeTLS.lookup t).getD false
      ⟨.returned (.ok old),{w with activeTLS := (t,b)::w.activeTLS.filter (fun p => p.1 != t)},events⟩
    | .tlsRestore t b =>
      ⟨.returned (.ok ()),{w with activeTLS := (t,b)::w.activeTLS.filter (fun p => p.1 != t)},events⟩
    | .allocate _ _ _ _ _ => ⟨.returned (.ok ()),w,events⟩
    | .release _ _ => ⟨.returned (.ok ()),w,events⟩
    | .spawn _ =>
      ⟨.returned (.ok (.granted w.nextHandle)),
        {w with liveHandles := w.nextHandle::w.liveHandles, nextHandle := w.nextHandle+1},events⟩
    | .join _ h =>
      ⟨.returned (.ok none),{w with liveHandles := w.liveHandles.filter (fun x => x != h)},events⟩
    | .cleanup _ => ⟨.returned (.ok ()),w,events⟩

/-- A separate denying world retains the native-confirmed spawn-denial branch.
No callback is executed in answering this request. -/
def denies {S : Type} (encode : {A : Type} → Request A → Bytes) (code : Int) : Runtime S where
  answer := fun {A} request w =>
    match request with
    | .spawn _ => ⟨.returned (.ok (.denied code)),w,
        [NativeEvent.side [118,50,54,51] (encode request)]⟩
    | r => (grants encode).answer r w

def spawn {S : Type} (runtime : Runtime S) (thread : Nat) : Q S Nat :=
  PV_V263_World.bind (runtime.answer (.spawn thread)) fun reply =>
    match reply with
    | .granted h => lift (.ok h)
    | .denied code => fun w => ⟨.fault (.spawnDenied code),w,[]⟩

/-- panic=abort client view; a spawn-denial panic cannot be caught as a source
Err, fail or divergence. The underlying runtime prefix/state is unchanged. -/
def aborting {A : Type} : Outcome A → Outcome A
  | .fault (.spawnDenied _) => .fault (.abort [])
  | .fault (.panic p) => .fault (.abort p)
  | r => r

theorem grant_spawn {S : Type} (encode : {A : Type} → Request A → Bytes)
    (t : Nat) (w : State S) :
    (spawn (grants encode) t w).outcome = .returned (.ok w.nextHandle) := rfl

theorem deny_spawn {S : Type} (encode : {A : Type} → Request A → Bytes)
    (t : Nat) (code : Int) (w : State S) :
    (spawn (denies encode code) t w).outcome = .fault (.spawnDenied code) := rfl

theorem denial_aborts {A : Type} (code : Int) :
    aborting (Outcome.fault (A := A) (.spawnDenied code)) = .fault (.abort []) := rfl

theorem deny_no_source {S : Type} (encode : {A : Type} → Request A → Bytes)
    (t : Nat) (code : Int) (w : State S) :
    sourceProjection (spawn (denies encode code) t w).outcome = none := rfl

#print axioms Request
#print axioms Runtime
#print axioms grants
#print axioms denies
#print axioms spawn
#print axioms aborting
#print axioms grant_spawn
#print axioms deny_spawn
#print axioms denial_aborts
#print axioms deny_no_source
end R1Z.PV_V263_WorkerRequests
