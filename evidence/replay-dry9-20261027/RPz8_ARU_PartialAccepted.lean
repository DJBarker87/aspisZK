import RPz8_ARU_SourceResults
import RPz8_ART_AccountAccepted
import RPz8_ART_WrapperExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_PartialAccepted
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
    SCE_Experiment.accepted (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a)).2 = true ∧
    eval H (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) =
      eval H (SCE_Experiment.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) := by
  let cfg := FIp_Install.configuration err c r
  have source := ARU_SourceResults.accepted L copy allocator c err r native1 native2 hashv extraction a H n
  have firstPartial : (eval H (ART_PartialAccount.wrapper hashv
      (ARS_NativeAccount.firstSyntax cfg hashv copy allocator CPH_Program.verifier (eval H a.first).2))).2 =
      ok (.Ok (n.entry.saved,n.entry.post1,n.entry.final1)) :=
    (congrArg Prod.snd (ART_WrapperExact.execution hashv H _ n.firstAgrees)).trans source.1
  have secondPartial : (eval H (ART_PartialAccount.wrapper hashv
      (ARS_NativeAccount.secondSyntax cfg hashv allocator CPH_Program.verifier
        (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2))).2 =
      ok (.Ok (n.entry.post2,n.entry.final2)) :=
    (congrArg Prod.snd (ART_WrapperExact.execution hashv H _ n.secondAgrees)).trans source.2
  have yes : SCE_Experiment.accepted (eval H (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a)).2 = true := by
    unfold ART_PartialAccount.account
    simp only [AspisV8R19.OracleProgramOps.eval_bind,firstPartial,secondPartial,eval,SCE_Experiment.accepted]
  exact ⟨yes,ART_AccountAccepted.exact cfg hashv copy allocator CPH_Program.verifier a H yes⟩

#print axioms accepted
end AspisR1.ARU_PartialAccepted
end
