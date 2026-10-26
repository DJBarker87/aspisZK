import R1Z.PDict_EventWorld244
import R1Z.PV_RunJoin_CallerWorld
import R1Z.PDict_RemainingDictionary231
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_World244
open Aeneas Aeneas.Std ProverRwFull

/-- An error observation at an OS reply. Payload resources are represented by
the world, not discarded by a forged native Error value. -/
structure Error where
  kind : core.io.error.ErrorKind
  message : List U8
  payload : Nat

instance fileDecidableEq : DecidableEq PDict_FileCarrier.File := by
  unfold PDict_FileCarrier.File
  infer_instance

inductive Request where
  | open64 (path : List U8) (flags mode : U32)
  | read (owner : PDict_FileCarrier.File) (count : Usize)
  | write (owner : PDict_FileCarrier.File) (bytes : List U8)
  | sync (owner : PDict_FileCarrier.File)
  | close (owner : PDict_FileCarrier.File)
  deriving DecidableEq

/-- Includes returned bytes, resources, errors and the observer's side channels.
No law for any of these fields is inferred from a successful source call. -/
structure Reply where
  outcome : core.result.Result (Usize × List U8) Error
  resources : List PDict_FileCarrier.File
  visible : List U8
  sideChannels : List Nat

abbrev Event := PDict_EventWorld244.Event Request Reply

/-- The entropy component is literally the sibling interface. Filesystem replies
extend it; they do not reset, replace, or reinterpret its128entropy positions. -/
abbrev World (E : Type) :=
  PDict_EventWorld244.World (PV_RunJoin_CallerWorld.RawTape E) Request Reply

def step {E : Type} (request : Request) (world : World E) :
    Option (Reply × World E) := PDict_EventWorld244.step request world

/-- These are named environmental outcome predicates, NOT axioms or a source
refinement hypothesis. A concrete OS world must supply the relevant predicate
for each consumed event. Its probability/availability law is not proved here. -/
structure Laws (E : Type) where
  open64 : World E → List U8 → U32 → U32 → Reply → Prop
  read : World E → PDict_FileCarrier.File → Usize → Reply → Prop
  write : World E → PDict_FileCarrier.File → List U8 → Reply → Prop
  sync : World E → PDict_FileCarrier.File → Reply → Prop
  close : World E → PDict_FileCarrier.File → Reply → Prop

def permitted {E : Type} (laws : Laws E) (world : World E)
    (request : Request) (reply : Reply) : Prop :=
  match request with
  | .open64 path flags mode => laws.open64 world path flags mode reply
  | .read owner count => laws.read world owner count reply
  | .write owner bytes => laws.write world owner bytes reply
  | .sync owner => laws.sync world owner reply
  | .close owner => laws.close world owner reply

/-- A law is supplied at the complete pre-call world, including history and
both cursors. It is not inferred from an execution equality or from E1. -/
def Allowed {E : Type} (laws : Laws E) (world : World E)
    (request : Request) (reply : Reply) (next : World E) : Prop :=
  step request world = some (reply,next) ∧ permitted laws world request reply

theorem step_at {E : Type} (world : World E) (event : Event)
    (position : world.files[world.fileUsed]? = some event) :
    step event.request world =
      some (event.reply, { world with fileUsed := world.fileUsed + 1 }) := by
  exact PDict_EventWorld244.step_at world event position

theorem exhausted {E : Type} (world : World E) (request : Request)
    (position : world.files[world.fileUsed]? = none) : step request world = none := by
  exact PDict_EventWorld244.exhausted world request position

theorem entropy_signature (E : Type) :
    PV_RunJoin_CallerWorld.RawTape E =
      (Fin 128 → ((Fin 64 → Fin 256) × Option E)) := rfl

#print axioms fileDecidableEq
#print axioms entropy_signature
#print axioms step_at
#print axioms exhausted
end R1Z.PDict_World244
