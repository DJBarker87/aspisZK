import ARV_Adaptive
import ARQ_Installation
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_AdaptiveAccepted
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment

theorem accepted {A C : Type}
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (H : Bytes → State) (address : Bytes) (original : State)
    (different : H address ≠ original)
    (i : FirstInputs A) (j : SecondInputs A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record)) (final1 final2 : A)
    (firstAgrees : ARS_QueryTransport.Agrees H (SdkC_Source.run hashv
      (ARS_NativeAccount.firstSyntax (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier i) []).2)
    (secondAgrees : ARS_QueryTransport.Agrees H (SdkC_Source.run hashv
      (ARS_NativeAccount.secondSyntax (FIp_Install.configuration err c r) hashv allocator CPH_Program.verifier (ARV_Constant.poison j)) []).2)
    (yes1 : first native1 copy allocator i.entry CPH_Program.verifier i.data i.state =
      ok (.Ok (saved,post1,final1)))
    (yes2 : second native2 allocator j.entry CPH_Program.verifier j.data j.slot j.state =
      ok (.Ok (post2,final2))) :
    SCE_Experiment.accepted (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier (ARV_Adaptive.adversary i j address original))).2 = true := by
  let cfg := FIp_Install.configuration err c r
  have ext : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk cfg.adapter cfg.currentBase cfg.stageBase cfg.finish cfg.reserved
        cfg.query cfg.geometry cfg.boundaries cfg.std) native1 native2 hashv := by
    rw [←ARQ_Installation.dictionary err c r]
    exact extraction
  have f := (congrArg Prod.snd (ART_WrapperExact.execution hashv H _ firstAgrees)).trans
    (ARU_WrapperSource.first cfg.adapter cfg.currentBase cfg.stageBase cfg.finish cfg.reserved
      cfg.query cfg.geometry cfg.boundaries cfg.std hashv copy allocator i.entry CPH_Program.verifier
      i.data i.state native1 native2 ext saved post1 final1 yes1)
  have poisoned := ARV_PoisonNative.accepted native2 allocator j.entry CPH_Program.verifier
    j.data j.slot j.state final2 post2 yes2
  have s := (congrArg Prod.snd (ART_WrapperExact.execution hashv H _ secondAgrees)).trans
    (ARU_WrapperSource.second cfg.adapter cfg.currentBase cfg.stageBase cfg.finish cfg.reserved
      cfg.query cfg.geometry cfg.boundaries cfg.std hashv allocator (ARV_Poison.entry j.entry)
      CPH_Program.verifier j.data j.slot j.state native1 native2 ext (ARV_Poison.entry j.entry).heap final2 poisoned)
  unfold ART_PartialAccount.account ARV_Adaptive.adversary
  simp only [eval_bind,eval,ARS_NativeAccount.firstSyntax,ARS_NativeAccount.secondSyntax,ARV_Constant.poison,if_neg different]
  rw [f]
  simp only [eval_bind,eval,ARS_NativeAccount.secondSyntax,ARV_Constant.poison,if_neg different]
  rw [s]
  rfl

#print axioms accepted
end AspisR1.ARV_AdaptiveAccepted
end
