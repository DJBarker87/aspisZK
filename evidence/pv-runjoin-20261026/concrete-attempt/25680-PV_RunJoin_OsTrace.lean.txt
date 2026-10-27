import R1Z.PV_RunJoin_OsWorld
set_option autoImplicit false
namespace R1Z.PV_RunJoin_OsTrace
open Aeneas Aeneas.Std PV_RunJoin_OsWorld
variable {E File Reply Time Worker : Type}

/-- The complete retained effect consumed. No observer component is erased:
reply decoding can retain errors, resources, visible bytes and side channels. -/
structure Prefix (File Reply Time Worker : Type) where
  files : List (Event (Request File) Reply)
  times : List Time
  workers : List Worker

def consumed (world : World E File Reply Time Worker) : Prefix File Reply Time Worker :=
  ⟨world.files.take world.fileUsed,world.time.take world.timeUsed,
    world.workers.take world.workerUsed⟩

/-- Decoder DATA: installing a decoder requires equality with the actual
native complete observer. A successful source return does not supply it. -/
structure Decoder (File Reply Time Worker Observation : Type) where
  decode : Prefix File Reply Time Worker → Observation

def observe {Observation : Type} (decoder : Decoder File Reply Time Worker Observation)
    (world : World E File Reply Time Worker) : Observation := decoder.decode (consumed world)

theorem same_complete_prefix {Observation : Type}
    (decoder : Decoder File Reply Time Worker Observation)
    (left right : World E File Reply Time Worker)
    (files : left.files.take left.fileUsed = right.files.take right.fileUsed)
    (times : left.time.take left.timeUsed = right.time.take right.timeUsed)
    (workers : left.workers.take left.workerUsed = right.workers.take right.workerUsed) :
    observe decoder left = observe decoder right := by
  unfold observe consumed
  rw [files,times,workers]

#print consumed
#print Decoder
#print axioms same_complete_prefix
end R1Z.PV_RunJoin_OsTrace
