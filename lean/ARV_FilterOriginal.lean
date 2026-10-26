import ARV_FilterPreserves
import ARU_OriginalFactory
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_FilterOriginal
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)

theorem preserved
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (native H : Bytes → State)
    (n : ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a native)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native)
    (consistent : ARS_AccountReplay.Consistent
      (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H) :
    eval H (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) =
      eval native (ART_Runtime.runtime (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) := by
  obtain ⟨⟨m⟩,same⟩ := ARU_OriginalFactory.original L copy allocator c err r native1 native2 hashv extraction a native H n syscall consistent
  rw [ARV_FilterPreserves.supported L copy allocator c err r native1 native2 hashv a H m,
    ART_Runtime.eval_runtime,ART_Runtime.eval_runtime,same]

#print axioms preserved
end AspisR1.ARV_FilterOriginal
end
