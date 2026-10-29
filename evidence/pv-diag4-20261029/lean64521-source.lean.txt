import R1Z.PV_RunJoin_CallerWorld
set_option autoImplicit false
namespace R1Z.PV_RunJoin_OsWorld
open Aeneas Aeneas.Std

/-- File carriers and replies must be identified with PDict_World244.File and
Reply by the deployment interpretation. No fresh opaque native handle is made. -/
inductive Request (File : Type) where
  | open64 (path : List U8) (flags mode : U32)
  | read (owner : File) (count : Usize)
  | write (owner : File) (bytes : List U8)
  | sync (owner : File)
  | close (owner : File)
  deriving DecidableEq

structure Event (Q R : Type) where
  request : Q
  reply : R

/-- Same entropy signature and file event/cursor shape as PDict_World244;
time and scheduling are additional native effect inputs, never entropy coins. -/
structure World (E File Reply Time Worker : Type) where
  entropy : PV_RunJoin_CallerWorld.RawTape E
  entropyUsed : Nat
  files : List (Event (Request File) Reply)
  fileUsed : Nat
  time : List Time
  timeUsed : Nat
  workers : List Worker
  workerUsed : Nat

variable {E File Reply Time Worker : Type}

def fileStep [DecidableEq File] (request : Request File)
    (world : World E File Reply Time Worker) :
    Option (Reply × World E File Reply Time Worker) := do
  let event ← world.files[world.fileUsed]?
  if event.request = request then
    some (event.reply,{world with fileUsed := world.fileUsed + 1})
  else none

def timeStep (world : World E File Reply Time Worker) :
    Option (Time × World E File Reply Time Worker) := do
  let outcome ← world.time[world.timeUsed]?
  some (outcome,{world with timeUsed := world.timeUsed + 1})

def workerStep (world : World E File Reply Time Worker) :
    Option (Worker × World E File Reply Time Worker) := do
  let outcome ← world.workers[world.workerUsed]?
  some (outcome,{world with workerUsed := world.workerUsed + 1})

/-- Named outcome predicates. These are DATA, not assumed validity proofs.
An actual OS interpretation supplies each law at the complete pre-call world. -/
structure Laws (E File Reply Time Worker : Type) where
  entropyDraw : World E File Reply Time Worker → Nat →
    PV_RunJoin_CallerWorld.RawReply E → Prop
  open64 : World E File Reply Time Worker → List U8 → U32 → U32 → Reply → Prop
  read : World E File Reply Time Worker → File → Usize → Reply → Prop
  write : World E File Reply Time Worker → File → List U8 → Reply → Prop
  sync : World E File Reply Time Worker → File → Reply → Prop
  close : World E File Reply Time Worker → File → Reply → Prop
  time : World E File Reply Time Worker → Time → Prop
  worker : World E File Reply Time Worker → Worker → Prop

def permitted (laws : Laws E File Reply Time Worker)
    (world : World E File Reply Time Worker) (request : Request File) (reply : Reply) : Prop :=
  match request with
  | .open64 path flags mode => laws.open64 world path flags mode reply
  | .read owner count => laws.read world owner count reply
  | .write owner bytes => laws.write world owner bytes reply
  | .sync owner => laws.sync world owner reply
  | .close owner => laws.close world owner reply

def EntropyAllowed (laws : Laws E File Reply Time Worker)
    (world : World E File Reply Time Worker) (i : Fin 128)
    (reply : PV_RunJoin_CallerWorld.RawReply E) : Prop :=
  world.entropyUsed = i.val ∧ world.entropy i = reply ∧ laws.entropyDraw world i.val reply

def FileAllowed [DecidableEq File] (laws : Laws E File Reply Time Worker)
    (world : World E File Reply Time Worker) (request : Request File) (reply : Reply)
    (next : World E File Reply Time Worker) : Prop :=
  fileStep request world = some (reply,next) ∧ permitted laws world request reply

def TimeAllowed (laws : Laws E File Reply Time Worker)
    (world : World E File Reply Time Worker) (outcome : Time)
    (next : World E File Reply Time Worker) : Prop :=
  timeStep world = some (outcome,next) ∧ laws.time world outcome

def WorkerAllowed (laws : Laws E File Reply Time Worker)
    (world : World E File Reply Time Worker) (outcome : Worker)
    (next : World E File Reply Time Worker) : Prop :=
  workerStep world = some (outcome,next) ∧ laws.worker world outcome

/-- Unix File::flush is pure in the sibling's checked dictionary and consumes
no OS event. Durability sync remains a distinct request with an outcome law. -/
def flush (world : World E File Reply Time Worker) := world

theorem file_at [DecidableEq File] (world : World E File Reply Time Worker)
    (event : Event (Request File) Reply)
    (at_position : world.files[world.fileUsed]? = some event) :
    fileStep event.request world =
      some (event.reply,{world with fileUsed := world.fileUsed + 1}) := by
  simp [fileStep,at_position]

theorem time_at (world : World E File Reply Time Worker) (outcome : Time)
    (at_position : world.time[world.timeUsed]? = some outcome) :
    timeStep world = some (outcome,{world with timeUsed := world.timeUsed + 1}) := by
  simp [timeStep,at_position]

theorem worker_at (world : World E File Reply Time Worker) (outcome : Worker)
    (at_position : world.workers[world.workerUsed]? = some outcome) :
    workerStep world = some (outcome,{world with workerUsed := world.workerUsed + 1}) := by
  simp [workerStep,at_position]

theorem flush_frame (world : World E File Reply Time Worker) : flush world = world := rfl

#print Laws
#print EntropyAllowed
#print FileAllowed
#print TimeAllowed
#print WorkerAllowed
#print axioms file_at
#print axioms time_at
#print axioms worker_at
#print axioms flush_frame
end R1Z.PV_RunJoin_OsWorld
