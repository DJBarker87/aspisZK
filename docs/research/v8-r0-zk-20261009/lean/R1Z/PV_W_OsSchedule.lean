import R1Z.PV_W_OsFile
set_option autoImplicit false
namespace R1Z.PV_W_OsSchedule
open PV_W_Threading PV_RunJoin_OsWorld PV_W_OsFile
variable {E File Reply Time Worker Fs Allocator Extra C Value : Type}

abbrev Update (Value Fs Allocator Extra : Type) :=
  Value → Fs → PV_W_Enriched.Process Allocator Extra → Fs × PV_W_Enriched.Process Allocator Extra

def after (update : Update Value Fs Allocator Extra) (value : Value)
    (w : Full E File Reply Time Worker Fs Allocator Extra)
    (nextOs : World E File Reply Time Worker) : Full E File Reply Time Worker Fs Allocator Extra :=
  let next := update value w.filesystem w.process
  ⟨nextOs,next.1,next.2⟩

def time (update : Update Time Fs Allocator Extra)
    (tag : Time → World E File Reply Time Worker → C) :
    M (Full E File Reply Time Worker Fs Allocator Extra) C Fault Time := fun w =>
  match timeStep w.os with
  | none => ⟨.fail .timeTape,w,[]⟩
  | some (outcome,nextOs) => ⟨.ok outcome,after update outcome w nextOs,[(w,tag outcome nextOs)]⟩

def worker (update : Update Worker Fs Allocator Extra)
    (tag : Worker → World E File Reply Time Worker → C) :
    M (Full E File Reply Time Worker Fs Allocator Extra) C Fault Worker := fun w =>
  match workerStep w.os with
  | none => ⟨.fail .workerTape,w,[]⟩
  | some (outcome,nextOs) => ⟨.ok outcome,after update outcome w nextOs,[(w,tag outcome nextOs)]⟩

def TimeStep (update : Update Time Fs Allocator Extra)
    (tag : Time → World E File Reply Time Worker → C)
    (w : Full E File Reply Time Worker Fs Allocator Extra) (c : C)
    (next : Full E File Reply Time Worker Fs Allocator Extra) : Prop :=
  ∃ outcome nextOs, timeStep w.os = some (outcome,nextOs) ∧
    c = tag outcome nextOs ∧ next = after update outcome w nextOs

def WorkerStep (update : Update Worker Fs Allocator Extra)
    (tag : Worker → World E File Reply Time Worker → C)
    (w : Full E File Reply Time Worker Fs Allocator Extra) (c : C)
    (next : Full E File Reply Time Worker Fs Allocator Extra) : Prop :=
  ∃ outcome nextOs, workerStep w.os = some (outcome,nextOs) ∧
    c = tag outcome nextOs ∧ next = after update outcome w nextOs

theorem time_matched (update : Update Time Fs Allocator Extra)
    (tag : Time → World E File Reply Time Worker → C)
    (w : Full E File Reply Time Worker Fs Allocator Extra) (outcome : Time)
    (nextOs : World E File Reply Time Worker) (matched : timeStep w.os = some (outcome,nextOs)) :
    time update tag w = ⟨.ok outcome,after update outcome w nextOs,[(w,tag outcome nextOs)]⟩ := by
  simp only [time,matched]

theorem worker_matched (update : Update Worker Fs Allocator Extra)
    (tag : Worker → World E File Reply Time Worker → C)
    (w : Full E File Reply Time Worker Fs Allocator Extra) (outcome : Worker)
    (nextOs : World E File Reply Time Worker) (matched : workerStep w.os = some (outcome,nextOs)) :
    worker update tag w = ⟨.ok outcome,after update outcome w nextOs,[(w,tag outcome nextOs)]⟩ := by
  simp only [worker,matched]

theorem time_valid (update : Update Time Fs Allocator Extra)
    (tag : Time → World E File Reply Time Worker → C) : Valid (TimeStep update tag) (time update tag) := by
  intro w
  cases matched : timeStep w.os with
  | none =>
    simp only [time,matched]
    exact .nil w
  | some pair =>
    rcases pair with ⟨outcome,nextOs⟩
    rw [time_matched update tag w outcome nextOs matched]
    exact .cons ⟨outcome,nextOs,matched,rfl,rfl⟩ (.nil _)

theorem worker_valid (update : Update Worker Fs Allocator Extra)
    (tag : Worker → World E File Reply Time Worker → C) : Valid (WorkerStep update tag) (worker update tag) := by
  intro w
  cases matched : workerStep w.os with
  | none =>
    simp only [worker,matched]
    exact .nil w
  | some pair =>
    rcases pair with ⟨outcome,nextOs⟩
    rw [worker_matched update tag w outcome nextOs matched]
    exact .cons ⟨outcome,nextOs,matched,rfl,rfl⟩ (.nil _)

#print axioms time_matched
#print axioms worker_matched
#print axioms time_valid
#print axioms worker_valid
end R1Z.PV_W_OsSchedule
