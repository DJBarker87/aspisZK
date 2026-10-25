import Hir_Search
import RawJ_InstalledBudget
import Hiq_RecordedBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_LifetimeExperiment
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel Hir_WriterSelect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
abbrev Recorded (A : Type) := Output (Call A) × List (CallAt A)
abbrev Execution (A : Type) := Recorded A × GExq_AccountExperiment.SecondReply A

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

/-- A SINGLE scheduler followed by the selected TX2. The selected TX1 is read
from already recorded executions, never replayed as another native invocation. -/
def program (initial : Store) (schedule : Schedule A (Call A)) : Program Bytes State (Execution A) :=
  bind (Hir_Recorded.program c hashv native1 copy allocator id initial schedule) fun recorded =>
    bind (Hir_PartialOracle.program hashv
      (secondCode c hashv allocator id recorded.1.1 recorded.1.2.2)) fun reply =>
        .done (recorded,reply)

def pairOf (execution : Execution A) : Option (GExq_AccountExperiment.Outcome A) :=
  let recorded := execution.1
  let out := recorded.1
  let chosen := out.2.2
  match search native1 copy allocator id (chosen.layout.handles 6).1
      (out.1 (chosen.layout.handles 6).1).data recorded.2 with
  | none => none
  | some writer => some (Hir_FirstChoice.input writer.site.before writer.site.call,
      .ok (.Ok (writer.saved,writer.post,writer.final)),
      some (Hir_Choice.input out.1 chosen,execution.2))

def select (execution : Execution A) : R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
  match pairOf native1 copy allocator id execution with
  | none => (⟨[],[]⟩,⟨[],[]⟩)
  | some pair => Hiq_ByteSelection.select (DrvC_Installation.sdk c) id pair

end AspisR1.Hir_LifetimeExperiment
end
