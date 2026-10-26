import ARU_SourceResults
import ART_WrapperExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_FirstPartial
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
theorem accepted {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) :
    (eval H (ART_PartialAccount.wrapper hashv
      (ARS_NativeAccount.firstSyntax (FIp_Install.configuration err c r) hashv copy allocator
        CPH_Program.verifier (eval H a.first).2))).2 = ok (.Ok (n.entry.saved,n.entry.post1,n.entry.final1)) := by
  exact (congrArg Prod.snd (ART_WrapperExact.execution hashv H _ n.firstAgrees)).trans
    (ARU_SourceResults.accepted L copy allocator c err r native1 native2 hashv extraction a H n).1

#print axioms accepted
end AspisR1.ARV_FirstPartial
end
