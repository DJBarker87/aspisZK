import RPz8_SCE_Projection
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_PublicProjection
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment F3T_ByteCarrier

theorem bytes {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State) (run : RunView)
    (observed : (eval H (runtime c hashv copy allocator id a)).2 = some run) :
    run.2.1.physical.bytes = (eval H (submission a)).2.publicBytes := by
  rw [SCE_Projection.input_projection c hashv copy allocator id a H run observed,
    F3T_Canon.canon_eval,lift_eval]
  rfl
#print axioms bytes
end AspisR1.SCE_PublicProjection
end
