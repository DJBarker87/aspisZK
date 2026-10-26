import ARU_Factory
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_Coverage
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
theorem original {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (native H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a native)
    (consistent : ARS_AccountReplay.Consistent
      (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H) :
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) ∧
    eval H (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) =
      eval native (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) := by
  exact ⟨ARU_Factory.deployed L copy allocator c err r native1 native2 hashv extraction a native H n consistent,
    ARS_AccountReplay.replay _ native H consistent⟩

#print axioms original
end AspisR1.ARU_Coverage
end
