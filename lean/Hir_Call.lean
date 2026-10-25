import Hir_PartialPrefix
import Hiq_NativeHistory
import Hiq_DrvExperiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_Call
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers GExq_AccountExperiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

structure Call (A : Type) where
  layout : Layout
  data : Slice U8
  slot : S2W_ExtractionBoundary.Slot
  state : A

abbrev Reply (A : Type) := Sum (FirstReply A) (SecondReply A)
abbrev Effect (A : Type) := Store × S2X.AccountEvent × Reply A

def firstEffect {A : Type} (store : Store) (call : Call A) (reply : FirstReply A) : Effect A :=
  match reply with
  | .ok (.Ok (saved,_,_)) =>
    (commit store (call.layout.handles 2).1 saved,
      .committedWrite (call.layout.handles 2).1 (MultiproofConeCanonical.bytesOf saved.val),.inl reply)
  | _ => (store,.rollback,.inl reply)

def native {A : Type} (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store) (call : Call A) : Effect A :=
  match Hiq_ReleaseRoute.route call.data with
  | .first => firstEffect store call
      (first native1 copy allocator (load store call.layout) id call.data call.state)
  | .second => (store,.rollback,.inr
      (second native2 allocator (load store call.layout) id call.data call.slot call.state))
  | .reject => (store,.rollback,.inr (.ok (.Err .InvalidInstructionData)))

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

def firstCode (store : Store) (call : Call A) :=
  GExq_InstalledWrapper.first c.adapter c.currentBase (AuS1_Install.base c.stageBase)
    c.finish c.reserved c.query c.geometry c.boundaries c.std hashv copy allocator
    (load store call.layout) id call.data call.state

def secondCode (store : Store) (call : Call A) :=
  GExq_InstalledWrapper.second c.adapter c.currentBase (AuS1_Install.base c.stageBase)
    c.finish c.reserved c.query c.geometry c.boundaries c.std hashv allocator
    (load store call.layout) id call.data call.slot call.state

/-- Actual source wrapper syntax, including allocator, copy and cleanup
failures. The dispatcher chooses exactly one child. Rollback affects ledger
state; a rejected child's prior successful oracle reads remain in the log. -/
def oracle (store : Store) (call : Call A) : Program Bytes State (Effect A) :=
  match Hiq_ReleaseRoute.route call.data with
  | .first => bind (Hir_PartialOracle.program hashv (firstCode c hashv copy allocator id store call))
      (fun reply => .done (firstEffect store call reply))
  | .second => bind (Hir_PartialOracle.program hashv (secondCode c hashv allocator id store call))
      (fun reply => .done (store,.rollback,.inr reply))
  | .reject => .done (store,.rollback,.inr (.ok (.Err .InvalidInstructionData)))

end AspisR1.Hir_Call
end
