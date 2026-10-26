import SCE_FailureZero
import SCE_AccountBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_AccountMass
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A)

/-- Exact event expression for the constructed account observer. All source
queries remain in its physical log; no hypothetical source pair is inserted. -/
theorem pointwise (H : Bytes → State) :
    F3T_Runtime.runtimeMass (eval H (runtime c hashv copy allocator id a)) =
      RawRecordedOracleExtractionMassBin.failureMass
        (view ((eval H (account c hashv copy allocator id a)).1,
          (F3T_Canon.canonInput (F3T_ByteCarrier.input c
            (submitted (eval H (account c hashv copy allocator id a)).2.1)),
           accepted (eval H (account c hashv copy allocator id a)).2))) := by
  rw [runtime_eval]
  rfl

#print axioms pointwise
end AspisR1.SCE_AccountMass
end
