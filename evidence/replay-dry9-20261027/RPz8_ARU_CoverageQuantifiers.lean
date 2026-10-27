import RPz8_ARU_PartialFactory
import RPz8_ARU_AllWorld
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_CoverageQuantifiers
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
/-- Exact residual original-law coverage. No new trust or adopted promise. -/
def OriginalCoverage {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (a : Adversary A) : Prop :=
  ∀ H, SCE_Experiment.accepted (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
    hashv copy allocator CPH_Program.verifier a)).2 = true →
    ∃ native, ARS_AccountReplay.Consistent
      (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H ∧
      Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a native)

theorem exact_iff {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) :
    OriginalCoverage (Tx := Tx) L copy allocator c err r native1 native2 hashv a ↔
      ARU_AllWorld.Supported (Tx := Tx) L copy allocator c err r native1 native2 hashv a := by
  constructor
  · intro coverage H accepted
    obtain ⟨native,consistent,⟨original⟩⟩ := coverage H accepted
    exact ARU_PartialFactory.original L copy allocator c err r native1 native2 hashv extraction a native H original consistent
  · intro support H accepted
    exact ⟨H,(by intro address member; rfl),support H accepted⟩

#print axioms exact_iff
end AspisR1.ARU_CoverageQuantifiers
end
