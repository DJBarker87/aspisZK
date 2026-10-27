import SCE_Execution
import P2P_NativeSelection
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_Selection
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment SCE_Execution

/-- One fixed selector of the actual response-selected entries, valid even if
TX2 rejects. There is no H-selected constant function in the experiment. -/
theorem actual {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (ops : AdapterRw.Ops) (a : Adversary A) (H : Bytes → State)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (first : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 =
      .ok (.Ok (saved,post,final))) :
    Hiq_ByteSelection.select ops id (eval H (account c hashv copy allocator id a)).2 =
      let i := (eval H a.first).2
      let next := (eval H (a.second i saved post final)).2
      P2P_NativeSelection.pair ops id i.entry next.entry next.data next.slot := by
  rw [SCE_Execution.accepted_eval c hashv copy allocator id a H saved post final first]
  rfl

#print axioms actual
end AspisR1.SCG_Selection
end
