import R1Z.PV_RunJoin_OsWorld
import R1Z.PV_W_Enriched
set_option autoImplicit false
namespace R1Z.PV_W_OsFile
open PV_W_Threading PV_RunJoin_OsWorld

/-- A missing/mismatched interpreter tape is distinct from a native IO Err,
which remains a value inside the reply. Neither is silently made successful. -/
inductive Fault where
  | extraction (error : Aeneas.Std.Error)
  | fileTape
  | entropyCursor
  | timeTape
  | workerTape

abbrev Full (E File Reply Time Worker Fs Allocator Extra : Type) :=
  PV_W_Enriched.World (World E File Reply Time Worker) Fs Allocator Extra

variable {E File Reply Time Worker Fs Allocator Extra C : Type} [DecidableEq File]
abbrev Update (File Reply Fs Allocator Extra : Type) :=
  Request File → Reply → Fs → PV_W_Enriched.Process Allocator Extra →
    Fs × PV_W_Enriched.Process Allocator Extra

def afterFile (update : Update File Reply Fs Allocator Extra)
    (request : Request File) (reply : Reply)
    (w : Full E File Reply Time Worker Fs Allocator Extra)
    (nextOs : World E File Reply Time Worker) : Full E File Reply Time Worker Fs Allocator Extra :=
  let next := update request reply w.filesystem w.process
  ⟨nextOs,next.1,next.2⟩

def file (update : Update File Reply Fs Allocator Extra)
    (tag : Request File → Reply → World E File Reply Time Worker → C)
    (request : Request File) : M (Full E File Reply Time Worker Fs Allocator Extra) C Fault Reply := fun w =>
  match fileStep request w.os with
  | none => ⟨.fail .fileTape,w,[]⟩
  | some (reply,nextOs) =>
    ⟨.ok reply,afterFile update request reply w nextOs,[(w,tag request reply nextOs)]⟩

/-- Tape consumption and the chosen memory/filesystem effect are explicit
model transitions. This definition asserts no native OS transition law. -/
def Step (update : Update File Reply Fs Allocator Extra)
    (tag : Request File → Reply → World E File Reply Time Worker → C)
    (w : Full E File Reply Time Worker Fs Allocator Extra) (c : C)
    (next : Full E File Reply Time Worker Fs Allocator Extra) : Prop :=
  ∃ request reply nextOs, fileStep request w.os = some (reply,nextOs) ∧
    c = tag request reply nextOs ∧ next = afterFile update request reply w nextOs

theorem file_matched (update : Update File Reply Fs Allocator Extra)
    (tag : Request File → Reply → World E File Reply Time Worker → C)
    (request : Request File) (w : Full E File Reply Time Worker Fs Allocator Extra)
    (reply : Reply) (nextOs : World E File Reply Time Worker)
    (matched : fileStep request w.os = some (reply,nextOs)) :
    file update tag request w =
      ⟨.ok reply,afterFile update request reply w nextOs,[(w,tag request reply nextOs)]⟩ := by
  simp only [file,matched]

theorem file_rejected (update : Update File Reply Fs Allocator Extra)
    (tag : Request File → Reply → World E File Reply Time Worker → C)
    (request : Request File) (w : Full E File Reply Time Worker Fs Allocator Extra)
    (mismatch : fileStep request w.os = none) :
    file update tag request w = ⟨.fail .fileTape,w,[]⟩ := by
  simp only [file,mismatch]

theorem file_valid (update : Update File Reply Fs Allocator Extra)
    (tag : Request File → Reply → World E File Reply Time Worker → C)
    (request : Request File) : Valid (Step update tag) (file update tag request) := by
  intro w
  cases matched : fileStep request w.os with
  | none =>
    rw [file_rejected update tag request w matched]
    exact .nil w
  | some pair =>
    rcases pair with ⟨reply,nextOs⟩
    rw [file_matched update tag request w reply nextOs matched]
    exact .cons ⟨request,reply,nextOs,matched,rfl,rfl⟩ (.nil _)

/-- A tape failure after prior effects keeps their state and ordered prefix. -/
theorem file_failure_prefix {A : Type}
    (update : Update File Reply Fs Allocator Extra)
    (tag : Request File → Reply → World E File Reply Time Worker → C)
    (request : Request File) (m : M (Full E File Reply Time Worker Fs Allocator Extra) C Fault A)
    (w : Full E File Reply Time Worker Fs Allocator Extra) (a : A)
    (returned : (m w).outcome = .ok a)
    (mismatch : fileStep request (m w).world.os = none) :
    PV_W_Threading.bind m (fun _ => file update tag request) w =
      ⟨.fail .fileTape,(m w).world,(m w).calls⟩ := by
  rw [bind_ok m _ w a returned,file_rejected update tag request (m w).world mismatch]
  simp only [List.append_nil]

#print axioms file_matched
#print axioms file_rejected
#print axioms file_valid
#print axioms file_failure_prefix
end R1Z.PV_W_OsFile
