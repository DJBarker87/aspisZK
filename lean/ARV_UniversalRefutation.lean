import ARV_OneTuple
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_UniversalRefutation
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open GExq_AccountExperiment SCE_Experiment

theorem from_one_tuple {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (native : Bytes → State)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a native) :
    ¬ (∀ b : Adversary A,
      Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv b native) →
      ARU_AllWorld.Supported (Tx := Tx) L copy allocator c err r native1 native2 hashv b) := by
  intro universal
  obtain ⟨b,original,H,accepted,noSupport,noAll,noCoverage⟩ :=
    ARV_OneTuple.obstruction L copy allocator c err r native1 native2 hashv extraction a native syscall n
  exact noAll (universal b original)

#print axioms from_one_tuple
end AspisR1.ARV_UniversalRefutation
end
