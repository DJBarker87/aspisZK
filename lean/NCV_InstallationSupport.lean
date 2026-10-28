import NCV_Install
import NCF_EntryContract
set_option autoImplicit false
noncomputable section
namespace NCV_InstallationSupport
open Aeneas Aeneas.Std Result AspisR1

def configure {F E : Type} (missing : DrvC_Installation.Configuration F E) :
    DrvC_Installation.Configuration F E :=
  {missing with adapter:=NCV_Install.install missing.adapter}

theorem selected {F E : Type} (missing : DrvC_Installation.Configuration F E) :
    (configure missing).adapter.op48=NCV_Install.op48 ∧
    (configure missing).adapter.op49=NCV_Install.op49 ∧
    (configure missing).adapter.op50=NCV_Install.op50 := ⟨rfl,rfl,rfl⟩

theorem sdk_master {F E : Type} (missing : DrvC_Installation.Configuration F E) :
    (DrvC_Installation.sdk (configure missing)).op48=NCV_Install.op48 := rfl

theorem sdk_checkpoint {F E : Type} (missing : DrvC_Installation.Configuration F E) :
    (DrvC_Installation.sdk (configure missing)).op49=NCV_Install.op49 := rfl

theorem sdk_lane {F E : Type} (missing : DrvC_Installation.Configuration F E) :
    (DrvC_Installation.sdk (configure missing)).op50=NCV_Install.op50 := rfl

/-- Reuse the existing symbolic row representability law, without asserting a
native iterator association or decoder result. -/
theorem represented_rows (read : Nat → U64) (start count : Nat) (initial : Nat → U64) :
    (List.range count).map (fun k=>NBX_RowFrames.writeRows read start count initial (start+k))=
      NBX_FrameComposition.sequenceRows read start count :=
  NBX_SequenceResult.returned read start count initial

#print axioms selected
#print axioms sdk_master
#print axioms sdk_checkpoint
#print axioms sdk_lane
#print axioms represented_rows
end NCV_InstallationSupport
end
