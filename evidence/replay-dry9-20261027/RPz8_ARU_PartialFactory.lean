import RPz8_ARU_PartialAccepted
import RPz8_ARU_Factory
import RPz8_ARS_WorldCylinder
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_PartialFactory
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
      (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H) :
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) := by
  let cfg := FIp_Install.configuration err c r
  have original := ARU_PartialAccepted.accepted L copy allocator c err r native1 native2 hashv extraction a native n
  have same := ARS_AccountReplay.replay _ native H consistent
  have yes : SCE_Experiment.accepted (eval H (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a)).2 = true := by
    rw [same]; exact original.1
  have idealSame : eval H (account cfg hashv copy allocator CPH_Program.verifier a) =
      eval native (account cfg hashv copy allocator CPH_Program.verifier a) :=
    (ART_AccountAccepted.exact cfg hashv copy allocator CPH_Program.verifier a H yes).symm.trans
      (same.trans original.2)
  exact ARU_Factory.deployed L copy allocator c err r native1 native2 hashv extraction a native H n
    (ARS_WorldCylinder.agrees_of_same native H _ idealSame)

#print axioms original
end AspisR1.ARU_PartialFactory
end
