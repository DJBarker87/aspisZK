import R1Z.PV_RunJoin_Deployed
import R1Z.PV_W_OsEntropy
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RuntimeInit35
open Aeneas Aeneas.Std
variable [ProverRwFull.ExternalTypes]
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable {Coins E N L File Reply Time Worker Fs Allocator Extra : Type}

/-- Complete initialization data, including all native statuses and all
process/filesystem state. Native association and its joint law are retained
P obligations; these inputs are not assumed to be uniformly sampled. -/
structure Input (Coins E N L File Reply Time Worker Fs Allocator Extra : Type) where
  entropy : Coins → PV_RunJoin_CallerWorld.RawTape E
  policy : Coins → N
  ledger : Coins → L
  files : Coins → List (PV_RunJoin_OsWorld.Event (PV_RunJoin_OsWorld.Request File) Reply)
  time : Coins → List Time
  workers : Coins → List Worker
  filesystem : Coins → Fs
  process : Coins → PV_W_Enriched.Process Allocator Extra

variable (d : Input Coins E N L File Reply Time Worker Fs Allocator Extra)

def world (c : Coins) : PV_W_OsFile.Full E File Reply Time Worker Fs Allocator Extra :=
  ⟨⟨d.entropy c,0,d.files c,0,d.time c,0,d.workers c,0⟩,d.filesystem c,d.process c⟩

def completion (error : E → ProverRwRngCaller.getrandom.error.Error) :
    PV_RunJoin_CompletedWorld.Data Coins N L (PV_W_OsFile.Full E File Reply Time Worker Fs Allocator Extra) :=
  ⟨fun c i => PV_RunJoin_CallerWorld.reply error (d.entropy c i),d.policy,d.ledger,world d⟩

def initial (error : E → ProverRwRngCaller.getrandom.error.Error) (c : Coins) :
    PV_RunJoin_UnifiedRetry.State N L (PV_W_OsFile.Full E File Reply Time Worker Fs Allocator Extra) :=
  ⟨PV_RunJoin_CallerWorld.provider error (d.entropy c),d.policy c,d.ledger c,world d c⟩

/-- The exact completed source provider, including error replies, agrees
with the PV_W entropy input at the same completion coordinate. -/
theorem provider (error : E → ProverRwRngCaller.getrandom.error.Error) (c : Coins) :
    PV_RunJoin_CompletedWorld.provider (completion d error) c =
      (initial d error c).provider := rfl

theorem cursors (c : Coins) :
    (world d c).os.entropyUsed=0 ∧ (world d c).os.fileUsed=0 ∧
      (world d c).os.timeUsed=0 ∧ (world d c).os.workerUsed=0 := ⟨rfl,rfl,rfl,rfl⟩

theorem process (c : Coins) : (world d c).process=d.process c := rfl

theorem draw_first (update : PV_W_OsEntropy.Update E Fs Allocator Extra)
    {C : Type} (tag : Fin 128 → PV_RunJoin_CallerWorld.RawReply E → C) (c : Coins) :
    PV_W_OsEntropy.draw update tag ⟨0,by decide⟩ (world d c) =
      ⟨.ok (d.entropy c ⟨0,by decide⟩),
        PV_W_OsEntropy.afterDraw update ⟨0,by decide⟩ (world d c),
        [(world d c,tag ⟨0,by decide⟩ (d.entropy c ⟨0,by decide⟩))]⟩ :=
  PV_W_OsEntropy.draw_at update tag _ _ rfl

#print axioms provider
#print axioms cursors
#print axioms process
#print axioms draw_first
end R1Z.PV_RunJoin_RuntimeInit35
