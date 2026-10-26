import ARU_PartialFactory
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_ObservedSupport
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)

/-- Diagnostic observation predicate. This is NONCOMPUTABLE and is NOT a
source-certified runtime admission implementation or an adopted game change. -/
def Eligible (v : List (Bytes × State) × GExq_AccountExperiment.Outcome A) : Prop :=
  ∃ H, eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
    hashv copy allocator CPH_Program.verifier a) = v ∧
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)

theorem at_eval
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (H : Bytes → State) :
    Eligible (Tx := Tx) L copy allocator c err r native1 native2 hashv a
      (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)) ↔
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) := by
  constructor
  · rintro ⟨native,same,⟨n⟩⟩
    exact ARU_PartialFactory.original L copy allocator c err r native1 native2 hashv extraction a native H n
      (ARS_WorldCylinder.agrees_of_same native H _ same.symm)
  · intro n
    exact ⟨H,rfl,n⟩

#print axioms at_eval
end AspisR1.ARV_ObservedSupport
end
