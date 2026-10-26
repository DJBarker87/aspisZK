import ART_PhysicalView
import ART_Runtime
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_RuntimeMass
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
theorem pointwise {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A) (H : Bytes → State) :
    F3T_Runtime.runtimeMass (eval H (ART_Runtime.runtime c hashv copy allocator id a)) =
      RawRecordedOracleExtractionMassBin.failureMass (ART_PhysicalView.physical c hashv copy allocator id a H) := by
  rw [ART_Runtime.eval_runtime]
  rfl

#print axioms pointwise
end AspisR1.ARU_RuntimeMass
end
